(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

open Type_check
open Ast
open Ast_util
open Rewriter
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based sail-to-lem pprinter
****************************************************************************)

let opt_sequential = ref false
let opt_mwords = ref false

type context = {
  early_ret : bool;
  bound_nexps : NexpSet.t;
}
let empty_ctxt = { early_ret = false; bound_nexps = NexpSet.empty }

let print_to_from_interp_value = ref false
let langlebar = string "<|"
let ranglebar = string "|>"
let anglebars = enclose langlebar ranglebar

let is_number_char c =
  c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5' ||
  c = '6' || c = '7' || c = '8' || c = '9'

let rec fix_id remove_tick name = match name with
  | "assert"
  | "lsl"
  | "lsr"
  | "asr"
  | "type"
  | "fun"
  | "function"
  | "raise"
  | "try"
  | "match"
  | "with"
  | "check"
  | "field"
  | "LT"
  | "GT"
  | "EQ"
  | "integer"
    -> name ^ "'"
  | _ ->
     if String.contains name '#' then
       fix_id remove_tick (String.concat "_" (Util.split_on_char '#' name))
     else if String.contains name '?' then
       fix_id remove_tick (String.concat "_pat_" (Util.split_on_char '?' name))
     else if name.[0] = '\'' then
       let var = String.sub name 1 (String.length name - 1) in
       if remove_tick then var else (var ^ "'")
     else if is_number_char(name.[0]) then
       ("v" ^ name ^ "'")
     else name

let doc_id_lem (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_lem_type (Id_aux(i,_)) =
  match i with
  | Id("int") -> string "ii"
  | Id("nat") -> string "ii"
  | Id("option") -> string "maybe"
  | Id i -> string (fix_id false i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_lem_ctor (Id_aux(i,_)) =
  match i with
  | Id("bit") -> string "bitU"
  | Id("int") -> string "integer"
  | Id("nat") -> string "integer"
  | Id("Some") -> string "Just"
  | Id("None") -> string "Nothing"
  | Id i -> string (fix_id false (String.capitalize i))
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     separate space [colon; string (String.capitalize x); empty]

let doc_var_lem kid = string (fix_id true (string_of_kid kid))

let simple_annot l typ = (Parse_ast.Generated l, Some (Env.empty, typ, no_effect))
let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, Parse_ast.Generated l)),
  simple_annot (Parse_ast.Generated l)
    (atom_typ (Nexp_aux (Nexp_constant n, Parse_ast.Generated l))))

let effectful_set =
  List.exists
    (fun (BE_aux (eff,_)) ->
      match eff with
      | BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem
      | BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_nondet
      | BE_escape -> true
      | _ -> false)

let effectful (Effect_aux (Effect_set effs, _)) = effectful_set effs

let is_regtyp (Typ_aux (typ, _)) env = match typ with
  | Typ_app(id, _) when string_of_id id = "register" -> true
  | _ -> false

let doc_nexp_lem nexp =
  let (Nexp_aux (nexp, l) as full_nexp) = nexp_simp nexp in
  match nexp with
  | Nexp_constant i -> string ("ty" ^ Big_int.to_string i)
  | Nexp_var v -> string (string_of_kid (orig_kid v))
  | _ ->
     let rec mangle_nexp (Nexp_aux (nexp, _)) = begin
       match nexp with
       | Nexp_id id -> string_of_id id
       | Nexp_var kid -> string_of_id (id_of_kid (orig_kid kid))
       | Nexp_constant i -> Pretty_print_lem_ast.lemnum Big_int.to_string i
       | Nexp_times (n1, n2) -> mangle_nexp n1 ^ "_times_" ^ mangle_nexp n2
       | Nexp_sum (n1, n2) -> mangle_nexp n1 ^ "_plus_" ^ mangle_nexp n2
       | Nexp_minus (n1, n2) -> mangle_nexp n1 ^ "_minus_" ^ mangle_nexp n2
       | Nexp_exp n -> "exp_" ^ mangle_nexp n
       | Nexp_neg n -> "neg_" ^ mangle_nexp n
       | _ ->
          raise (Reporting_basic.err_unreachable l
                   ("cannot pretty-print nexp \"" ^ string_of_nexp full_nexp ^ "\"")) 
     end in
     string ("'" ^ mangle_nexp full_nexp)

(* Rewrite mangled names of type variables to the original names *)
let rec orig_nexp (Nexp_aux (nexp, l)) =
  let rewrap nexp = Nexp_aux (nexp, l) in
  match nexp with
  | Nexp_var kid -> rewrap (Nexp_var (orig_kid kid))
  | Nexp_times (n1, n2) -> rewrap (Nexp_times (orig_nexp n1, orig_nexp n2))
  | Nexp_sum (n1, n2) -> rewrap (Nexp_sum (orig_nexp n1, orig_nexp n2))
  | Nexp_minus (n1, n2) -> rewrap (Nexp_minus (orig_nexp n1, orig_nexp n2))
  | Nexp_exp n -> rewrap (Nexp_exp (orig_nexp n))
  | Nexp_neg n -> rewrap (Nexp_neg (orig_nexp n))
  | _ -> rewrap nexp

(* Returns the set of type variables that will appear in the Lem output,
   which may be smaller than those in the Sail type.  May need to be
   updated with doc_typ_lem *)
let rec lem_nexps_of_typ (Typ_aux (t,_)) =
  let trec = lem_nexps_of_typ in
  match t with
  | Typ_id _ -> NexpSet.empty
  | Typ_var kid -> NexpSet.singleton (orig_nexp (nvar kid))
  | Typ_fn (t1,t2,_) -> NexpSet.union (trec t1) (trec t2)
  | Typ_tup ts ->
     List.fold_left (fun s t -> NexpSet.union s (trec t))
       NexpSet.empty ts
  | Typ_app(Id_aux (Id "vector", _), [
    Typ_arg_aux (Typ_arg_nexp m, _);
    Typ_arg_aux (Typ_arg_order ord, _);
    Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
     let m = nexp_simp m in
     if !opt_mwords && is_bit_typ elem_typ && not (is_nexp_constant m) then
       NexpSet.singleton (orig_nexp m)
     else trec elem_typ
  | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
     trec etyp
  | Typ_app(Id_aux (Id "range", _),_)
  | Typ_app(Id_aux (Id "implicit", _),_)
  | Typ_app(Id_aux (Id "atom", _), _) -> NexpSet.empty
  | Typ_app (_,tas) ->
     List.fold_left (fun s ta -> NexpSet.union s (lem_nexps_of_typ_arg ta))
       NexpSet.empty tas
  | Typ_exist (kids,_,t) -> trec t
and lem_nexps_of_typ_arg (Typ_arg_aux (ta,_)) =
  match ta with
  | Typ_arg_nexp nexp -> NexpSet.singleton (nexp_simp (orig_nexp nexp))
  | Typ_arg_typ typ -> lem_nexps_of_typ typ
  | Typ_arg_order _ -> NexpSet.empty

let lem_tyvars_of_typ typ =
  NexpSet.fold (fun nexp ks -> KidSet.union ks (tyvars_of_nexp nexp))
    (lem_nexps_of_typ typ) KidSet.empty

(* When making changes here, check whether they affect lem_tyvars_of_typ *)
let doc_typ_lem, doc_atomic_typ_lem =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ true ty
    and typ' ty = fn_typ false ty
    and fn_typ atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_fn(arg,ret,efct) ->
         let ret_typ =
           if effectful efct
           then separate space [string "M"; fn_typ true ret]
           else separate space [fn_typ false ret] in
         let arg_typs = match arg with
           | Typ_aux (Typ_tup typs, _) ->
              List.map (app_typ false) typs
           | _ -> [tup_typ false arg] in
         let tpp = separate (space ^^ arrow ^^ space) (arg_typs @ [ret_typ]) in
         (* once we have proper excetions we need to know what the exceptions type is *)
         if atyp_needed then parens tpp else tpp
      | _ -> tup_typ atyp_needed ty
    and tup_typ atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_tup typs ->
         parens (separate_map (space ^^ star ^^ space) (app_typ false) typs)
      | _ -> app_typ atyp_needed ty
    and app_typ atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_app(Id_aux (Id "vector", _), [
          Typ_arg_aux (Typ_arg_nexp m, _);
          Typ_arg_aux (Typ_arg_order ord, _);
          Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
         let tpp = match elem_typ with
           | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) when !opt_mwords ->
             string "mword " ^^ doc_nexp_lem (nexp_simp m)
             (* (match nexp_simp m with
               | (Nexp_aux(Nexp_constant i,_)) -> string "bitvector ty" ^^ doc_int i
               | (Nexp_aux(Nexp_var _, _)) -> separate space [string "bitvector"; doc_nexp m]
               | _ -> raise (Reporting_basic.err_unreachable l
                 "cannot pretty-print bitvector type with non-constant length")) *)
           | _ -> string "list" ^^ space ^^ typ elem_typ in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
         let tpp = string "register_ref regstate register_value " ^^ typ etyp in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
         (string "integer")
      | Typ_app(id,args) ->
         let tpp = (doc_id_lem_type id) ^^ space ^^ (separate_map space doc_typ_arg_lem args) in
         if atyp_needed then parens tpp else tpp
      | _ -> atomic_typ atyp_needed ty
    and atomic_typ atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_id (Id_aux (Id "bool",_)) -> string "bool"
      | Typ_id (Id_aux (Id "bit",_)) -> string "bitU"
      | Typ_id (id) ->
         (*if List.exists ((=) (string_of_id id)) regtypes
         then string "register"
         else*) doc_id_lem_type id
      | Typ_var v -> doc_var v
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ ty in
         if atyp_needed then parens tpp else tpp
      | Typ_exist (kids,_,ty) -> begin
         let tpp = typ ty in
         let visible_vars = lem_tyvars_of_typ ty in
         match List.filter (fun kid -> KidSet.mem kid visible_vars) kids with
         | [] -> if atyp_needed then parens tpp else tpp
         | bad -> raise (Reporting_basic.err_general l
                           ("Existential type variable(s) " ^
                               String.concat ", " (List.map string_of_kid bad) ^
                               " escape into Lem"))
      end
    and doc_typ_arg_lem (Typ_arg_aux(t,_)) = match t with
      | Typ_arg_typ t -> app_typ true t
      | Typ_arg_nexp n -> doc_nexp_lem (nexp_simp n)
      | Typ_arg_order o -> empty
  in typ', atomic_typ

(* Check for variables in types that would be pretty-printed and are not
   bound in the val spec of the function. *)
let contains_t_pp_var ctxt (Typ_aux (t,a) as typ) =
  NexpSet.diff (lem_nexps_of_typ typ) ctxt.bound_nexps
  |> NexpSet.exists (fun nexp -> not (is_nexp_constant nexp))

let replace_typ_size ctxt env (Typ_aux (t,a)) =
  match t with
  | Typ_app (Id_aux (Id "vector",_) as id, [Typ_arg_aux (Typ_arg_nexp size,_);ord;typ']) ->
     begin
       let is_equal nexp =
         prove env (NC_aux (NC_equal (size,nexp),Parse_ast.Unknown))
       in match List.find is_equal (NexpSet.elements ctxt.bound_nexps) with
       | nexp -> Some (Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp nexp,Parse_ast.Unknown);ord;typ']),a))
       | exception Not_found -> None
     end
  | _ -> None

let doc_tannot_lem ctxt env eff typ =
  let of_typ typ =
    let ta = doc_typ_lem typ in
    if eff then string " : M " ^^ parens ta
    else string " : " ^^ ta
  in
  if contains_t_pp_var ctxt typ
  then
    match replace_typ_size ctxt env typ with
    | None -> empty
    | Some typ -> of_typ typ
  else of_typ typ

let doc_lit_lem (L_aux(lit,l)) =
  match lit with
  | L_unit  -> utf8string "()"
  | L_zero  -> utf8string "B0"
  | L_one   -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i ->
     let ipp = Big_int.to_string i in
     utf8string (
       if Big_int.less i Big_int.zero then "((0"^ipp^"):ii)"
       else "("^ipp^":ii)")
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     utf8string "(failwith \"undefined value of unsupported type\")"
  | L_string s -> utf8string ("\"" ^ s ^ "\"")
  | L_real s ->
    (* Lem does not support decimal syntax, so we translate a string
       of the form "x.y" into the ratio (x * 10^len(y) + y) / 10^len(y).
       The OCaml library has a conversion function from strings to floats, but
       not from floats to ratios. ZArith's Q library does have the latter, but
       using this would require adding a dependency on ZArith to Sail. *)
    let parts = Util.split_on_char '.' s in
    let (num, denom) = match parts with
    | [i] -> (Big_int.of_string i, Big_int.of_int 1)
    | [i;f] ->
      let denom = Big_int.pow_int_positive 10 (String.length f) in
      (Big_int.add (Big_int.mul (Big_int.of_string i) denom) (Big_int.of_string f), denom)
    | _ ->
      raise (Reporting_basic.Fatal_error
        (Reporting_basic.Err_syntax_locn (l, "could not parse real literal"))) in
    parens (separate space (List.map string [
      "realFromFrac"; Big_int.to_string num; Big_int.to_string denom]))

(* typ_doc is the doc for the type being quantified *)
let doc_quant_item vars_included (QI_aux (qi, _)) = match qi with
| QI_id (KOpt_aux (KOpt_none kid, _))
| QI_id (KOpt_aux (KOpt_kind (_, kid), _)) ->
   (match vars_included with
     None -> doc_var kid
   | Some set -> (*when KidSet.mem kid set -> doc_var kid*)
      let nexps = NexpSet.filter (fun nexp -> KidSet.mem (orig_kid kid) (nexp_frees nexp)) set in
      separate_map space doc_nexp_lem (NexpSet.elements nexps)
   | _ -> empty)
| _ -> empty

let doc_typquant_items_lem vars_included (TypQ_aux(tq,_)) = match tq with
| TypQ_tq qs -> separate_map space (doc_quant_item vars_included) qs
| _ -> empty

let doc_typquant_lem (TypQ_aux(tq,_)) vars_included typ = match tq with
| TypQ_tq ((_ :: _) as qs) ->
  string "forall " ^^ separate_map space (doc_quant_item vars_included) qs ^^ string ". " ^^ typ
| _ -> typ

(* Produce Size type constraints for bitvector sizes when using
   machine words.  Often these will be unnecessary, but this simple
   approach will do for now. *)

let rec typeclass_nexps (Typ_aux(t,_)) =
  if !opt_mwords then
    match t with
    | Typ_id _
    | Typ_var _
      -> NexpSet.empty
    | Typ_fn (t1,t2,_) -> NexpSet.union (typeclass_nexps t1) (typeclass_nexps t2)
    | Typ_tup ts -> List.fold_left NexpSet.union NexpSet.empty (List.map typeclass_nexps ts)
    | Typ_app (Id_aux (Id "vector",_),
               [Typ_arg_aux (Typ_arg_nexp size_nexp,_);
                _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)])
    | Typ_app (Id_aux (Id "itself",_),
               [Typ_arg_aux (Typ_arg_nexp size_nexp,_)]) ->
       let size_nexp = nexp_simp size_nexp in
       if is_nexp_constant size_nexp then NexpSet.empty else
       NexpSet.singleton (orig_nexp size_nexp)
    | Typ_app _ -> NexpSet.empty
    | Typ_exist (kids,_,t) -> NexpSet.empty (* todo *)
  else NexpSet.empty

let doc_typclasses_lem t =
  let nexps = typeclass_nexps t in
  if NexpSet.is_empty nexps then (empty, NexpSet.empty) else
  (separate_map comma_sp (fun nexp -> string "Size " ^^ doc_nexp_lem nexp) (NexpSet.elements nexps) ^^ string " => ", nexps)

let doc_typschm_lem quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ_lem t in
  if quants
  then
    let nexps_used = lem_nexps_of_typ t in
    let ptyc, nexps_sizes = doc_typclasses_lem t in
    let nexps_to_include = NexpSet.union nexps_used nexps_sizes in
    if NexpSet.is_empty nexps_to_include
    then pt
    else doc_typquant_lem tq (Some nexps_to_include) (ptyc ^^ pt)
  else pt

let is_ctor env id = match Env.lookup_id id env with
| Enum _ | Union _ -> true
| _ -> false

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat_lem ctxt apat_needed (P_aux (p,(l,annot)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_lem_ctor id)
                       (parens (separate_map comma (doc_pat_lem ctxt true) pats)) in
    if apat_needed then parens ppp else ppp
  | P_app(id,[]) -> doc_id_lem_ctor id
  | P_lit lit  -> doc_lit_lem lit
  | P_wild -> underscore
  | P_id id ->
     begin match id with
     | Id_aux (Id "None",_) -> string "Nothing" (* workaround temporary issue *)
     | _ -> doc_id_lem id end
  | P_var(p,_) -> doc_pat_lem ctxt true p
  | P_as(p,id) -> parens (separate space [doc_pat_lem ctxt true p; string "as"; doc_id_lem id])
  | P_typ(Typ_aux (Typ_tup typs, _), P_aux (P_tup pats, _)) ->
     (* Isabelle does not seem to like type-annotated tuple patterns;
        it gives a syntax error. Avoid this by annotating the tuple elements instead *)
     let doc_elem typ pat =
       doc_pat_lem ctxt true (add_p_typ typ pat) in
     parens (separate comma_sp (List.map2 doc_elem typs pats))
  | P_typ(typ,p) ->
    let doc_p = doc_pat_lem ctxt true p in
    if contains_t_pp_var ctxt typ then doc_p
    else parens (doc_op colon doc_p (doc_typ_lem typ))
  | P_vector pats ->
     let ppp = brackets (separate_map semi (doc_pat_lem ctxt true) pats) in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     raise (Reporting_basic.err_unreachable l
       "vector concatenation patterns should have been removed before pretty-printing")
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat_lem ctxt apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat_lem ctxt false) pats))
  | P_list pats -> brackets (separate_map semi (doc_pat_lem ctxt false) pats) (*Never seen but easy in lem*)
  | P_cons (p,p') -> doc_op (string "::") (doc_pat_lem ctxt true p) (doc_pat_lem ctxt true p')
  | P_record (_,_) -> empty (* TODO *)

let rec typ_needs_printed (Typ_aux (t,_) as typ) = match t with
  | Typ_tup ts -> List.exists typ_needs_printed ts
  | Typ_app (Id_aux (Id "itself",_),_) -> true
  | Typ_app (_, targs) -> is_bitvector_typ typ || List.exists typ_needs_printed_arg targs
  | Typ_fn (t1,t2,_) -> typ_needs_printed t1 || typ_needs_printed t2
  | Typ_exist (kids,_,t) ->
     let visible_kids = KidSet.inter (KidSet.of_list kids) (lem_tyvars_of_typ t) in
     typ_needs_printed t && KidSet.is_empty visible_kids
  | _ -> false
and typ_needs_printed_arg (Typ_arg_aux (targ, _)) = match targ with
  | Typ_arg_typ t -> typ_needs_printed t
  | _ -> false

let contains_early_return exp =
  let e_app (f, args) =
    let rets, args = List.split args in
    (List.fold_left (||) (string_of_id f = "early_return") rets,
    E_app (f, args)) in
  fst (fold_exp
  { (Rewriter.compute_exp_alg false (||))
    with e_return = (fun (_, r) -> (true, E_return r)); e_app = e_app } exp)

let typ_id_of (Typ_aux (typ, l)) = match typ with
  | Typ_id id -> id
  | Typ_app (register, [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id id, _)), _)])
    when string_of_id register = "register" -> id
  | Typ_app (id, _) -> id
  | _ -> raise (Reporting_basic.err_unreachable l "failed to get type id")

let prefix_recordtype = true
let report = Reporting_basic.err_unreachable
let doc_exp_lem, doc_let_lem =
  let rec top_exp (ctxt : context) (aexp_needed : bool)
    (E_aux (e, (l,annot)) as full_exp) =
    let expY = top_exp ctxt true in
    let expN = top_exp ctxt false in
    let expV = top_exp ctxt in
    let liftR doc =
      if ctxt.early_ret && effectful (effect_of full_exp)
      then separate space [string "liftR"; parens (doc)]
      else doc in
    match e with
    | E_assign((LEXP_aux(le_act,tannot) as le), e) ->
       (* can only be register writes *)
       let t = typ_of_annot tannot in
       (match le_act (*, t, tag*) with
        | LEXP_vector_range (le,e2,e3) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id_lem id in
                 liftR ((prefix 2 1)
                   (string "write_reg_field_range")
                   (align (doc_lexp_deref_lem ctxt le ^/^
                      field_ref ^/^ expY e2 ^/^ expY e3 ^/^ expY e)))
            | _ ->
               let deref = doc_lexp_deref_lem ctxt le in
               liftR ((prefix 2 1)
                 (string "write_reg_range")
                 (align (deref ^/^ expY e2 ^/^ expY e3) ^/^ expY e)))
        | LEXP_vector (le,e2) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id_lem id in
                 let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot fannot)) then "write_reg_field_bit" else "write_reg_field_pos" in
                 liftR ((prefix 2 1)
                   (string call)
                   (align (doc_lexp_deref_lem ctxt le ^/^
                     field_ref ^/^ expY e2 ^/^ expY e)))
            | LEXP_aux (_, lannot) ->
               let deref = doc_lexp_deref_lem ctxt le in
               let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot lannot)) then "write_reg_bit" else "write_reg_pos" in
               liftR ((prefix 2 1) (string call)
               (deref ^/^ expY e2 ^/^ expY e))
           )
        | LEXP_field ((LEXP_aux (_, lannot) as le),id) ->
          let field_ref =
            doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^
            underscore ^^
            doc_id_lem id (*^^
            dot ^^
            string "set_field"*) in
           liftR ((prefix 2 1)
             (string "write_reg_field")
             (doc_lexp_deref_lem ctxt le ^^ space ^^
                field_ref ^/^ expY e))
        | LEXP_deref re ->
           liftR ((prefix 2 1) (string "write_reg") (expY re ^/^ expY e))
        | _ ->
           liftR ((prefix 2 1) (string "write_reg") (doc_lexp_deref_lem ctxt le ^/^ expY e)))
    | E_vector_append(le,re) ->
      raise (Reporting_basic.err_unreachable l
        "E_vector_append should have been rewritten before pretty-printing")
    | E_cons(le,re) -> doc_op (group (colon^^colon)) (expY le) (expY re)
    | E_if(c,t,e) ->
       let indent = match e with
         | E_aux (E_if _, _) -> 0
         | _ -> 2 in
       let epp =
         separate space [string "if";group (expY c)] ^^
           break 1 ^^
             (prefix 2 1 (string "then") (expN t)) ^^ (break 1) ^^
               (prefix indent 1 (string "else") (expN e)) in
       if aexp_needed then parens (align epp) else epp
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
       raise (report l "E_for should have been rewritten before pretty-printing")
    | E_loop _ ->
       raise (report l "E_loop should have been rewritten before pretty-printing")
    | E_let(leb,e) ->
       let epp = let_exp ctxt leb ^^ space ^^ string "in" ^^ hardline ^^ expN e in
       if aexp_needed then parens epp else epp
    | E_app(f,args) ->
       begin match f with
       (* temporary hack to make the loop body a function of the temporary variables *)
       | Id_aux (Id "foreach", _) ->
          begin
            match args with
            | [exp1; exp2; exp3; ord_exp; vartuple; body] ->
               let loopvar, body = match body with
                 | E_aux (E_let (LB_aux (LB_val (
                     P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _), _), _), body), _) -> id, body
                 | _ -> raise (Reporting_basic.err_unreachable l ("Unable to find loop variable in " ^ string_of_exp body)) in
               let combinator = match effectful (effect_of body), ord_exp with
                 | false, E_aux (E_lit (L_aux (L_false, _)), _) -> "foreach_dec"
                 | false, E_aux (E_lit (L_aux (L_true, _)), _) -> "foreach_inc"
                 | true, E_aux (E_lit (L_aux (L_false, _)), _) -> "foreachM_dec"
                 | true, E_aux (E_lit (L_aux (L_true, _)), _) -> "foreachM_inc"
                 | _ -> raise (Reporting_basic.err_unreachable l "Unable to figure out loop combinator") in
               let indices_pp = parens (separate_map comma expY [exp1; exp2; exp3]) in
               parens (
                   (prefix 2 1)
                     ((separate space) [string combinator; indices_pp; expY vartuple])
                     (parens
                        (prefix 1 1 (separate space [string "fun"; doc_id_lem loopvar; expY vartuple; arrow]) (expN body))
                     )
                 )
          | _ -> raise (Reporting_basic.err_unreachable l
             "Unexpected number of arguments for loop combinator")
          end
       | Id_aux (Id (("while" | "until") as combinator), _) ->
          begin
            match args with
            | [cond; varstuple; body] ->
               let csuffix = match effectful (effect_of cond), effectful (effect_of body) with
                 | false, false -> "_PP"
                 | false, true  -> "_PM"
                 | true,  false -> "_MP"
                 | true,  true  -> "_MM" in
               parens (
                   (prefix 2 1)
                     ((separate space) [string (combinator ^ csuffix); expY varstuple])
                     ((prefix 0 1)
                       (parens (prefix 1 1 (separate space [string "fun"; expY varstuple; arrow]) (expN cond)))
                       (parens (prefix 1 1 (separate space [string "fun"; expY varstuple; arrow]) (expN body))))
                 )
            | _ -> raise (Reporting_basic.err_unreachable l
               "Unexpected number of arguments for loop combinator")
          end
       | Id_aux (Id "early_return", _) ->
          begin
            match args with
            | [exp] ->
               let epp = separate space [string "early_return"; expY exp] in
               let aexp_needed, tepp =
                 if contains_t_pp_var ctxt (typ_of exp) ||
                    contains_t_pp_var ctxt (typ_of full_exp) then
                   aexp_needed, epp
                 else
                   let tannot = separate space [string "MR";
                     doc_atomic_typ_lem false (typ_of full_exp);
                     doc_atomic_typ_lem false (typ_of exp)] in
                   true, doc_op colon epp tannot in
               if aexp_needed then parens tepp else tepp
            | _ -> raise (Reporting_basic.err_unreachable l
               "Unexpected number of arguments for early_return builtin")
          end
       | _ ->
          begin match annot with
          | Some (env, _, _) when (is_ctor env f) ->
             let epp =
               match args with
               | [] -> doc_id_lem_ctor f
               | [arg] -> doc_id_lem_ctor f ^^ space ^^ expV true arg
               | _ ->
                  doc_id_lem_ctor f ^^ space ^^ 
                    parens (separate_map comma (expV false) args) in
             if aexp_needed then parens (align epp) else epp
          | _ ->
             let call, is_extern = match annot with
               | Some (env, _, _) when Env.is_extern f env "lem" ->
                 string (Env.get_extern f env "lem"), true
               | _ -> doc_id_lem f, false in
             let argspp = align (separate_map (break 1) (expV true) args) in
             let epp = align (call ^//^ argspp) in
             let (taepp,aexp_needed) =
               let env = env_of full_exp in
               let t = Env.expand_synonyms env (typ_of full_exp) in
               let eff = effect_of full_exp in
               if typ_needs_printed t
               then (align epp ^^ (doc_tannot_lem ctxt env (effectful eff) t), true)
               else (epp, aexp_needed) in
             liftR (if aexp_needed then parens (align taepp) else taepp)
          end
       end
    | E_vector_access (v,e) ->
      raise (Reporting_basic.err_unreachable l
        "E_vector_access should have been rewritten before pretty-printing")
    | E_vector_subrange (v,e1,e2) ->
      raise (Reporting_basic.err_unreachable l
        "E_vector_subrange should have been rewritten before pretty-printing")
    | E_field((E_aux(_,(l,fannot)) as fexp),id) ->
       let ft = typ_of_annot (l,fannot) in
       (match fannot with
        | Some(env, (Typ_aux (Typ_id tid, _)), _)
        | Some(env, (Typ_aux (Typ_app (tid, _), _)), _)
          when Env.is_record tid env ->
           let fname =
             if prefix_recordtype
             then (string (string_of_id tid ^ "_")) ^^ doc_id_lem id
             else doc_id_lem id in
           expY fexp ^^ dot ^^ fname
        | _ ->
           raise (report l "E_field expression with no register or record type"))
    | E_block [] -> string "()"
    | E_block exps -> raise (report l "Blocks should have been removed till now.")
    | E_nondet exps -> raise (report l "Nondet blocks not supported.")
    | E_id id | E_ref id ->
       let env = env_of full_exp in
       let typ = typ_of full_exp in
       let eff = effect_of full_exp in
       let base_typ = Env.base_typ_of env typ in
       if has_effect eff BE_rreg then
         let epp = separate space [string "read_reg";doc_id_lem id] in
         if is_bitvector_typ base_typ
         then liftR (parens (epp ^^ doc_tannot_lem ctxt env true base_typ))
         else liftR epp
       else if is_ctor env id then doc_id_lem_ctor id
       else doc_id_lem id
    | E_lit lit -> doc_lit_lem lit
    | E_cast(typ,e) ->
       expV aexp_needed e
    | E_tuple exps ->
       parens (separate_map comma expN exps)
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
       let recordtyp = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _) ->
           (* when Env.is_record tid env -> *)
           tid
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       let epp = anglebars (space ^^ (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp ctxt recordtyp) fexps)) ^^ space) in
       if aexp_needed then parens epp else epp
    | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
       let recordtyp = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _)
           when Env.is_record tid env ->
           tid
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       anglebars (doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp ctxt recordtyp) fexps))
    | E_vector exps ->
       let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
       let (start, len, order, etyp) =
         if is_vector_typ t then vector_typ_args_of t
         else raise (Reporting_basic.err_unreachable l
           "E_vector of non-vector type") in
       let dir,dir_out = if is_order_inc order then (true,"true") else (false, "false") in
       let start = match nexp_simp start with
         | Nexp_aux (Nexp_constant i, _) -> Big_int.to_string i
         | _ -> if dir then "0" else string_of_int (List.length exps) in
       let expspp =
         match exps with
         | [] -> empty
         | e :: es ->
            let (expspp,_) =
              List.fold_left
                (fun (pp,count) e ->
                  (pp ^^ semi ^^ (if count = 20 then break 0 else empty) ^^
                     expN e),
                  if count = 20 then 0 else count + 1)
                (expN e,0) es in
            align (group expspp) in
       let epp = brackets expspp in
       let (epp,aexp_needed) =
         if is_bit_typ etyp && !opt_mwords then
           let bepp = string "of_bits" ^^ space ^^ parens (align epp) in
           (bepp ^^ doc_tannot_lem ctxt (env_of full_exp) false t, true)
         else (epp,aexp_needed) in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update(v,e1,e2) ->
       raise (Reporting_basic.err_unreachable l
         "E_vector_update should have been rewritten before pretty-printing")
    | E_vector_update_subrange(v,e1,e2,e3) ->
       raise (Reporting_basic.err_unreachable l
        "E_vector_update should have been rewritten before pretty-printing")
    | E_list exps ->
       brackets (separate_map semi (expN) exps)
    | E_case(e,pexps) ->
       let only_integers e = expY e in
       let epp =
         group ((separate space [string "match"; only_integers e; string "with"]) ^/^
                  (separate_map (break 1) (doc_case ctxt) pexps) ^/^
                    (string "end")) in
       if aexp_needed then parens (align epp) else align epp
    | E_try (e, pexps) ->
       if effectful (effect_of e) then
         let try_catch = if ctxt.early_ret then "try_catchR" else "try_catch" in
         let epp =
           group ((separate space [string try_catch; expY e; string "(function "]) ^/^
                    (separate_map (break 1) (doc_case ctxt) pexps) ^/^
                      (string "end)")) in
         if aexp_needed then parens (align epp) else align epp
       else
         raise (Reporting_basic.err_todo l "Warning: try-block around pure expression")
    | E_throw e ->
       let epp = liftR (separate space [string "throw"; expY e]) in
       if aexp_needed then parens (align epp) else align epp
    | E_exit e -> liftR (separate space [string "exit"; expY e])
    | E_assert (e1,e2) ->
       let epp = liftR (separate space [string "assert_exp"; expY e1; expY e2]) in
       if aexp_needed then parens (align epp) else align epp
    | E_app_infix (e1,id,e2) ->
       raise (Reporting_basic.err_unreachable l
         "E_app_infix should have been rewritten before pretty-printing")
    | E_var(lexp, eq_exp, in_exp) ->
       raise (report l "E_vars should have been removed before pretty-printing")
    | E_internal_plet (pat,e1,e2) ->
       let epp =
         let b = match e1 with E_aux (E_if _,_) -> true | _ -> false in
         match pat with
         | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
            (separate space [expV b e1; string ">>"]) ^^ hardline ^^ expN e2
         | _ ->
            (separate space [expV b e1; string ">>= fun";
                             doc_pat_lem ctxt true pat;arrow]) ^^ hardline ^^ expN e2 in
       if aexp_needed then parens (align epp) else epp
    | E_internal_return (e1) ->
       separate space [string "return"; expY e1]
    | E_sizeof nexp ->
      (match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit_lem (L_aux (L_num i, l))
        | _ ->
          raise (Reporting_basic.err_unreachable l
            "pretty-printing non-constant sizeof expressions to Lem not supported"))
    | E_return r ->
      let ret_monad = if !opt_sequential then " : MR regstate" else " : MR" in
      let ta =
        if contains_t_pp_var ctxt (typ_of full_exp) || contains_t_pp_var ctxt (typ_of r)
        then empty
        else separate space
          [string ret_monad;
          parens (doc_typ_lem (typ_of full_exp));
          parens (doc_typ_lem (typ_of r))] in
      align (parens (string "early_return" ^//^ expV true r ^//^ ta))
    | E_constraint _ -> string "true"
    | E_comment _ | E_comment_struc _ -> empty
    | E_internal_cast _ | E_internal_exp _ | E_sizeof_internal _
    | E_internal_exp_user _ | E_internal_value _ ->
      raise (Reporting_basic.err_unreachable l
        "unsupported internal expression encountered while pretty-printing")
  and let_exp ctxt (LB_aux(lb,_)) = match lb with
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; doc_pat_lem ctxt true pat; equals])
              (top_exp ctxt false e)

  and doc_fexp ctxt recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id_lem id
      else doc_id_lem id in
    group (doc_op equals fname (top_exp ctxt true e))

  and doc_case ctxt = function
  | Pat_aux(Pat_exp(pat,e),_) ->
    group (prefix 3 1 (separate space [pipe; doc_pat_lem ctxt false pat;arrow])
                  (group (top_exp ctxt false e)))
  | Pat_aux(Pat_when(_,_,_),(l,_)) ->
    raise (Reporting_basic.err_unreachable l
      "guarded pattern expression should have been rewritten before pretty-printing")

  and doc_lexp_deref_lem ctxt ((LEXP_aux(lexp,(l,annot))) as le) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref_lem ctxt le;dot;doc_id_lem id])
    | LEXP_id id -> doc_id_lem id
    | LEXP_cast (typ,id) -> doc_id_lem id
    | LEXP_tup lexps -> parens (separate_map comma_sp (doc_lexp_deref_lem ctxt) lexps)
    | _ ->
       raise (Reporting_basic.err_unreachable l ("doc_lexp_deref_lem: Unsupported lexp"))
             (* expose doc_exp_lem and doc_let *)
  in top_exp, let_exp

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_lem (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> separate space [pipe; doc_id_lem_ctor id; string "of";
                                        parens (doc_typ_lem typ)]
  | Tu_id id -> separate space [pipe; doc_id_lem_ctor id]

let rec doc_range_lem (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef_lem (TD_aux(td, (l, annot))) = match td with
  | TD_abbrev(id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     doc_op equals
       (separate space [string "type"; doc_id_lem_type id; doc_typquant_items_lem None typq])
       (doc_typschm_lem false typschm)
  | TD_record(id,nm,typq,fs,_) ->
    let fname fid = if prefix_recordtype
                    then concat [doc_id_lem id;string "_";doc_id_lem_type fid;]
                    else doc_id_lem_type fid in
    let f_pp (typ,fid) =
      concat [fname fid;space;colon;space;doc_typ_lem typ; semi] in
    let rectyp = match typq with
      | TypQ_aux (TypQ_tq qs, _) ->
        let quant_item = function
          | QI_aux (QI_id (KOpt_aux (KOpt_none kid, _)), l)
          | QI_aux (QI_id (KOpt_aux (KOpt_kind (_, kid), _)), l) ->
            [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid, l)), l)]
          | _ -> [] in
        let targs = List.concat (List.map quant_item qs) in
        mk_typ (Typ_app (id, targs))
      | TypQ_aux (TypQ_no_forall, _) -> mk_id_typ id in
    let fs_doc = group (separate_map (break 1) f_pp fs) in
    (* let doc_field (ftyp, fid) =
      let reftyp =
        mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
          [mk_typ_arg (Typ_arg_typ rectyp);
           mk_typ_arg (Typ_arg_typ ftyp)])) in
      let rfannot = doc_tannot_lem empty_ctxt env false reftyp in
      let get, set =
        string "rec_val" ^^ dot ^^ fname fid,
        anglebars (space ^^ string "rec_val with " ^^
          (doc_op equals (fname fid) (string "v")) ^^ space) in
      let base_ftyp = match annot with
        | Some (env, _, _) -> Env.base_typ_of env ftyp
        | _ -> ftyp in
      let (start, is_inc) =
        try
          let (start, _, ord, _) = vector_typ_args_of base_ftyp in
          match nexp_simp start with
          | Nexp_aux (Nexp_constant i, _) -> (i, is_order_inc ord)
          | _ ->
            raise (Reporting_basic.err_unreachable Parse_ast.Unknown
              ("register " ^ string_of_id id ^ " has non-constant start index " ^ string_of_nexp start))
        with
        | _ -> (Big_int.zero, true) in
      doc_op equals
        (concat [string "let "; parens (concat [doc_id_lem id; underscore; doc_id_lem fid; rfannot])])
        (anglebars (concat [space;
          doc_op equals (string "field_name") (string_lit (doc_id_lem fid)); semi_sp;
          doc_op equals (string "field_start") (string (Big_int.to_string start)); semi_sp;
          doc_op equals (string "field_is_inc") (string (if is_inc then "true" else "false")); semi_sp;
          doc_op equals (string "get_field") (parens (doc_op arrow (string "fun rec_val") get)); semi_sp;
          doc_op equals (string "set_field") (parens (doc_op arrow (string "fun rec_val v") set)); space])) in *)
    doc_op equals
           (separate space [string "type"; doc_id_lem_type id; doc_typquant_items_lem None typq])
           ((*doc_typquant_lem typq*) (anglebars (space ^^ align fs_doc ^^ space))) ^^ hardline
    (* if !opt_sequential && string_of_id id = "regstate" then empty
    else separate_map hardline doc_field fs *)
  | TD_variant(id,nm,typq,ar,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> empty
      | Id_aux ((Id "write_kind"),_) -> empty
      | Id_aux ((Id "barrier_kind"),_) -> empty
      | Id_aux ((Id "trans_kind"),_) -> empty
      | Id_aux ((Id "instruction_kind"),_) -> empty
      (* | Id_aux ((Id "regfp"),_) -> empty
      | Id_aux ((Id "niafp"),_) -> empty
      | Id_aux ((Id "diafp"),_) -> empty *)
      | Id_aux ((Id "option"),_) -> empty
      | _ ->
         let ar_doc = group (separate_map (break 1) doc_type_union_lem ar) in
         let typ_pp =
           (doc_op equals)
             (concat [string "type"; space; doc_id_lem_type id; space; doc_typquant_items_lem None typq])
             ((*doc_typquant_lem typq*) ar_doc) in
         let make_id pat id =
           separate space [string "SIA.Id_aux";
                           parens (string "SIA.Id " ^^ string_lit (doc_id id));
                           if pat then underscore else string "SIA.Unknown"] in
         let fromInterpValueF = concat [doc_id_lem_type id;string "FromInterpValue"] in
         let toInterpValueF = concat [doc_id_lem_type id;string "ToInterpValue"] in
         let fromInterpValuePP =
           (prefix 2 1)
             (separate space [string "let rec";fromInterpValueF;string "v";equals;string "match v with"])
             (
               ((separate_map (break 1))
                  (fun (Tu_aux (tu,_)) ->
                    match tu with
                    | Tu_ty_id (ty,cid) ->
                       (separate space)
                         [pipe;string "SI.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                          arrow;
                          doc_id_lem_ctor cid;
                          parens (string "fromInterpValue v")]
                    | Tu_id cid ->
                       (separate space)
                         [pipe;string "SI.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                          arrow;
                          doc_id_lem_ctor cid])
                  ar) ^/^

                  ((separate space) [pipe;string "SI.V_tuple [v]";arrow;fromInterpValueF;string "v"]) ^/^

                 let failmessage =
                    (string_lit
                       (concat [string "fromInterpValue";space;doc_id_lem_type id;colon;space;string "unexpected value. ";]))
                    ^^
                      (string " ^ Interp.debug_print_value v") in
                  ((separate space) [pipe;string "v";arrow;string "failwith";parens failmessage]) ^/^
                 string "end") in
         let toInterpValuePP =
           (prefix 2 1)
             (separate space [string "let";toInterpValueF;equals;string "function"])
             (
               ((separate_map (break 1))
                  (fun (Tu_aux (tu,_)) ->
                    match tu with
                    | Tu_ty_id (ty,cid) ->
                       (separate space)
                         [pipe;doc_id_lem_ctor cid;string "v";arrow;
                          string "SI.V_ctor";
                          parens (make_id false cid);
                          parens (string "SIA.T_id " ^^ string_lit (doc_id id));
                          string "SI.C_Union";
                          parens (string "toInterpValue v")]
                    | Tu_id cid ->
                       (separate space)
                         [pipe;doc_id_lem_ctor cid;arrow;
                          string "SI.V_ctor";
                          parens (make_id false cid);
                          parens (string "SIA.T_id " ^^ string_lit (doc_id id));
                          string "SI.C_Union";
                          parens (string "toInterpValue ()")])
                  ar) ^/^
                 string "end") in
         let fromToInterpValuePP =
           ((prefix 2 1)
              (concat [string "instance ";parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
              (concat [string "let toInterpValue = ";toInterpValueF;hardline;
                       string "let fromInterpValue = ";fromInterpValueF]))
           ^/^ string "end" in
         typ_pp ^^ hardline ^^ hardline ^^
           if !print_to_from_interp_value then
           toInterpValuePP ^^ hardline ^^ hardline ^^
             fromInterpValuePP ^^ hardline ^^ hardline ^^
               fromToInterpValuePP ^^ hardline
           else empty)
  | TD_enum(id,nm,enums,_) ->
     (match id with
      | Id_aux ((Id "read_kind"),_) -> empty
      | Id_aux ((Id "write_kind"),_) -> empty
      | Id_aux ((Id "barrier_kind"),_) -> empty
      | Id_aux ((Id "trans_kind"),_) -> empty
      | Id_aux ((Id "instruction_kind"),_) -> empty
      | Id_aux ((Id "regfp"),_) -> empty
      | Id_aux ((Id "niafp"),_) -> empty
      | Id_aux ((Id "diafp"),_) -> empty
      | _ ->
         let rec range i j = if i > j then [] else i :: (range (i+1) j) in
         let nats = range 0 in
         let enums_doc = group (separate_map (break 1 ^^ pipe ^^ space) doc_id_lem_ctor enums) in
         let typ_pp = (doc_op equals)
                        (concat [string "type"; space; doc_id_lem_type id;])
                        (enums_doc) in
         let fromInterpValueF = concat [doc_id_lem_type id;string "FromInterpValue"] in
         let toInterpValueF = concat [doc_id_lem_type id;string "ToInterpValue"] in
         let make_id pat id =
           separate space [string "SIA.Id_aux";
                           parens (string "SIA.Id " ^^ string_lit (doc_id id));
                           if pat then underscore else string "SIA.Unknown"] in
         let fromInterpValuePP =
           (prefix 2 1)
             (separate space [string "let rec";fromInterpValueF;string "v";equals;string "match v with"])
             (
               ((separate_map (break 1))
                  (fun (cid) ->
                    (separate space)
                      [pipe;string "SI.V_ctor";parens (make_id true cid);underscore;underscore;string "v";
                       arrow;doc_id_lem_ctor cid]
                  )
                  enums
               ) ^/^
                 (
                   (align
                      ((prefix 3 1)
                         (separate space [pipe;string ("SI.V_lit (SIA.L_aux (SIA.L_num n) _)");arrow])
                         (separate space [string "match";parens(string "natFromInteger n");string "with"] ^/^
                            (
                              ((separate_map (break 1))
                                 (fun (cid,number) ->
                                   (separate space)
                                     [pipe;string (string_of_int number);arrow;doc_id_lem_ctor cid]
                                 )
                                 (List.combine enums (nats ((List.length enums) - 1)))
                              ) ^/^ string "end"
                            )
                         )
                      )
                   )
                 ) ^/^

                  ((separate space) [pipe;string "SI.V_tuple [v]";arrow;fromInterpValueF;string "v"]) ^/^

                   let failmessage =
                     (string_lit
                        (concat [string "fromInterpValue";space;doc_id_lem_type id;colon;space;string "unexpected value. ";]))
                     ^^
                       (string " ^ Interp.debug_print_value v") in
                   ((separate space) [pipe;string "v";arrow;string "failwith";parens failmessage]) ^/^

                     string "end") in
         let toInterpValuePP =
           (prefix 2 1)
             (separate space [string "let";toInterpValueF;equals;string "function"])
             (
               ((separate_map (break 1))
                  (fun (cid,number) ->
                    (separate space)
                      [pipe;doc_id_lem_ctor cid;arrow;
                       string "SI.V_ctor";
                       parens (make_id false cid);
                       parens (string "SIA.T_id " ^^ string_lit (doc_id id));
                       parens (string ("SI.C_Enum " ^ string_of_int number));
                       parens (string "toInterpValue ()")])
                  (List.combine enums (nats ((List.length enums) - 1)))) ^/^
                 string "end") in
         let fromToInterpValuePP =
           ((prefix 2 1)
             (concat [string "instance ";parens (string "ToFromInterpValue " ^^ doc_id_lem_type id)])
             (concat [string "let toInterpValue = ";toInterpValueF;hardline;
                      string "let fromInterpValue = ";fromInterpValueF]))
           ^/^ string "end" in
          typ_pp ^^ hardline ^^ hardline ^^
            if !print_to_from_interp_value 
            then toInterpValuePP ^^ hardline ^^ hardline ^^
              fromInterpValuePP ^^ hardline ^^ hardline ^^
                fromToInterpValuePP ^^ hardline
            else empty)
    | _ -> raise (Reporting_basic.err_unreachable l "register with non-constant indices")

let args_of_typ l env typ =
  let typs = match typ with
    | Typ_aux (Typ_tup typs, _) -> typs
    | typ -> [typ] in
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    P_aux (P_id id, (l, Some (env, typ, no_effect))),
    E_aux (E_id id, (l, Some (env, typ, no_effect))) in
  List.split (List.mapi arg typs)

let rec untuple_args_pat (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let (Typ_aux (taux, _)) = typ_of_annot annot in
  let identity = (fun body -> body) in
  match paux, taux with
  | P_tup [], _ ->
     let annot = (l, Some (Env.empty, unit_typ, no_effect)) in
     [P_aux (P_lit (mk_lit L_unit), annot)], identity
  | P_tup pats, _ -> pats, identity
  | P_wild, Typ_tup typs ->
     let wild typ = P_aux (P_wild, (l, Some (env, typ, no_effect))) in
     List.map wild typs, identity
  | P_typ (_, pat), _ -> untuple_args_pat pat
  | P_as _, Typ_tup _ | P_id _, Typ_tup _ ->
     let argpats, argexps = args_of_typ l env (pat_typ_of pat) in
     let argexp = E_aux (E_tuple argexps, annot) in
     let bindargs (E_aux (_, bannot) as body) =
       E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
     argpats, bindargs
  | _, _ ->
     [pat], identity

let doc_rec_lem force_rec (Rec_aux(r,_)) = match r with
  | Rec_nonrec when not force_rec -> space
  | _ -> space ^^ string "rec" ^^ space

let doc_tannot_opt_lem (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> (*doc_typquant_lem tq*) (doc_typ_lem typ)

let doc_fun_body_lem ctxt exp =
  let doc_exp = doc_exp_lem ctxt false exp in
  if ctxt.early_ret
  then align (string "catch_early_return" ^//^ parens (doc_exp))
  else doc_exp

let doc_funcl_lem (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let typ = typ_of_annot annot in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let ctxt =
    { early_ret = contains_early_return exp;
      bound_nexps = NexpSet.union (lem_nexps_of_typ typ) (typeclass_nexps typ) } in
  let pats, bind = untuple_args_pat pat in
  let patspp = separate_map space (doc_pat_lem ctxt true) pats in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting_basic.err_unreachable l
                "guarded pattern expression should have been rewritten before pretty-printing") in
  group (prefix 3 1
    (separate space [doc_id_lem id; patspp; equals])
    (doc_fun_body_lem ctxt (bind exp)))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_),_))::_ -> id

module StringSet = Set.Make(String)

let doc_fundef_rhs_lem (FD_aux(FD_function(r, typa, efa, funcls),fannot) as fd) =
  separate_map (hardline ^^ string "and ") doc_funcl_lem funcls

let doc_mutrec_lem = function
  | [] -> failwith "DEF_internal_mutrec with empty function list"
  | fundefs ->
     string "let rec " ^^
     separate_map (hardline ^^ string "and ") doc_fundef_rhs_lem fundefs

let rec doc_fundef_lem (FD_aux(FD_function(r, typa, efa, fcls),fannot) as fd) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  (* TODO: Move splitting of execute function to the rewriter *)
  (*| FCL_aux (FCL_Funcl(id,_),_) :: _
    when string_of_id id = "execute" (*|| string_of_id id = "initial_analysis"*) ->
    let (_,auxiliary_functions,clauses) =
      List.fold_left
        (fun (already_used_fnames,auxiliary_functions,clauses) funcl ->
          match funcl with
          | FCL_aux (FCL_Funcl (Id_aux (Id _,l),pexp),annot) ->
             let pat,guard,exp,(pexp_l,_) = destruct_pexp pexp in
             let _ = match guard with
               | None -> ()
               | _ ->
                  raise (Reporting_basic.err_unreachable pexp_l
                           "guarded pattern expression should have been rewritten before pretty-printing")
             in
             let ctor, l, argspat, pannot = (match pat with
               | P_aux (P_app (Id_aux (Id ctor,l),argspat),pannot) ->
                 (ctor, l, argspat, pannot)
               | P_aux (P_id (Id_aux (Id ctor,l)), pannot) ->
                 (ctor, l, [], pannot)
               | _ ->
                 raise (Reporting_basic.err_unreachable l
                   "unsupported parameter pattern in function clause")) in
             let rec pick_name_not_clashing_with already_used candidate =
               if StringSet.mem candidate already_used then
                 pick_name_not_clashing_with already_used (candidate ^ "'")
               else candidate in
             let unit_pat = P_aux (P_lit (mk_lit L_unit), (l, Some (Env.empty, unit_typ, no_effect))) in
             let aux_fname = pick_name_not_clashing_with already_used_fnames (string_of_id id ^ "_" ^ ctor) in
             let aux_args = if argspat = [] then unit_pat else P_aux (P_tup argspat,pannot) in
             let already_used_fnames = StringSet.add aux_fname already_used_fnames in
             let fcl = FCL_aux (FCL_Funcl (Id_aux (Id aux_fname,l),
                                           Pat_aux (Pat_exp (aux_args,exp),(pexp_l,None)))
                                  ,annot) in
             let auxiliary_functions =
                auxiliary_functions ^^ hardline ^^ hardline ^^
                  doc_fundef_lem (FD_aux (FD_function(r,typa,efa,[fcl]),fannot)) in
             (* Bind complex patterns to names so that we can pass them to the
                auxiliary function *)
             let name_pat idx (P_aux (p,a)) = match p with
               | P_as (pat,_) -> P_aux (p,a) (* already named *)
               | P_lit _ -> P_aux (p,a) (* no need to name a literal *)
               | P_id _ -> P_aux (p,a) (* no need to name an identifier *)
               | _ -> P_aux (P_as (P_aux (p,a), Id_aux (Id ("arg" ^ string_of_int idx),l)),a) in
             let named_argspat = List.mapi name_pat argspat in
             let named_pat = P_aux (P_app (Id_aux (Id ctor,l),named_argspat),pannot) in
             let named_args = if argspat = [] then [unit_pat] else named_argspat in
             let doc_arg idx (P_aux (p,(l,a))) = match p with
               | P_as (pat,id) -> doc_id_lem id
               | P_lit lit -> doc_lit_lem lit
               | P_id id -> doc_id_lem id
               | _ -> string ("arg" ^ string_of_int idx) in
             let clauses =
               clauses ^^ (break 1) ^^
                 (separate space
                    [pipe;doc_pat_lem empty_ctxt false named_pat;arrow;
                     string aux_fname;
                     separate space (List.mapi doc_arg named_args)]) in
             (already_used_fnames,auxiliary_functions,clauses)
        ) (StringSet.empty,empty,empty) fcls in

    auxiliary_functions ^^ hardline ^^ hardline ^^
    (prefix 2 1)
      ((separate space) [string "let" ^^ doc_rec_lem false r ^^ doc_id_lem id;equals;string "function"])
      (clauses ^/^ string "end")*)
  | FCL_aux (FCL_Funcl(id,_),annot) :: _
    when not (Env.is_extern id (env_of_annot annot) "lem") ->
    string "let" ^^ (doc_rec_lem (List.length fcls > 1) r) ^^ (doc_fundef_rhs_lem fd)
  | _ -> empty



let doc_dec_lem (DEC_aux (reg, ((l, _) as annot))) =
  match reg with
  | DEC_reg(typ,id) -> empty
     (* if !opt_sequential then empty
     else
       let env = env_of_annot annot in
       let rt = Env.base_typ_of env typ in
       if is_vector_typ rt then
         let (start, size, order, etyp) = vector_typ_args_of rt in
         if is_bit_typ etyp && is_nexp_constant start && is_nexp_constant size then
           let o = if is_order_inc order then "true" else "false" in
           (doc_op equals)
             (string "let" ^^ space ^^ doc_id_lem id)
             (string "Register" ^^ space ^^
                align (separate space [string_lit(doc_id_lem id);
                                       doc_nexp (size);
                                       doc_nexp (start);
                                       string o;
                                       string "[]"]))
           ^/^ hardline
         else raise (Reporting_basic.err_unreachable l ("can't deal with register type " ^ string_of_typ typ))
       else raise (Reporting_basic.err_unreachable l ("can't deal with register type " ^ string_of_typ typ)) *)
  | DEC_alias(id,alspec) -> empty
  | DEC_typ_alias(typ,id,alspec) -> empty

let doc_spec_lem (VS_aux (valspec,annot)) =
  match valspec with
  | VS_val_spec (typschm,id,ext,_) when ext "lem" = None ->
     (* let (TypSchm_aux (TypSchm_ts (tq, typ), _)) = typschm in
     if contains_t_pp_var typ then empty else *)
     separate space [string "val"; doc_id_lem id; string ":";doc_typschm_lem true typschm] ^/^ hardline 
  (* | VS_val_spec (_,_,Some _,_) -> empty *)
  | _ -> empty

let is_field_accessor regtypes fdef =
  let is_field_of regtyp field =
    List.exists (fun (tname, (_, _, fields)) -> tname = regtyp &&
      List.exists (fun (_, fid) -> string_of_id fid = field) fields) regtypes in
  match Util.split_on_char '_' (string_of_id (id_of_fundef fdef)) with
  | [access; regtyp; field] ->
     (access = "get" || access = "set") && is_field_of regtyp field
  | _ -> false

let doc_regtype_fields (tname, (n1, n2, fields)) =
  let i1, i2 = match n1, n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) -> i1, i2
    | _ -> raise (Reporting_basic.err_typ Parse_ast.Unknown
       ("Non-constant indices in register type " ^ tname)) in
  let dir_b = i1 < i2 in
  let dir = (if dir_b then "true" else "false") in
  let doc_field (fr, fid) =
    let i, j = match fr with
    | BF_aux (BF_single i, _) -> (i, i)
    | BF_aux (BF_range (i, j), _) -> (i, j)
    | _ -> raise (Reporting_basic.err_unreachable Parse_ast.Unknown
        ("Unsupported type in field " ^ string_of_id fid ^ " of " ^ tname)) in
    let fsize = Big_int.succ (Big_int.abs (Big_int.sub i j)) in
    (* TODO Assumes normalised, decreasing bitvector slices; however, since
       start indices or indexing order do not appear in Lem type annotations,
       this does not matter. *)
    let ftyp = vector_typ (nconstant fsize) dec_ord bit_typ in
    let reftyp =
      mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
        [mk_typ_arg (Typ_arg_typ (mk_id_typ (mk_id tname)));
         mk_typ_arg (Typ_arg_typ ftyp)])) in
    let rfannot = doc_tannot_lem empty_ctxt Env.empty false reftyp in
    doc_op equals
     (concat [string "let "; parens (concat [string tname; underscore; doc_id_lem fid; rfannot])])
     (concat [
       space; langlebar; string " field_name = \"" ^^ doc_id_lem fid ^^ string "\";"; hardline;
       space; space; space; string (" field_start = " ^ Big_int.to_string i ^ ";"); hardline;
       space; space; space; string (" field_is_inc = " ^ dir ^ ";"); hardline;
       space; space; space; string (" get_field = get_" ^ tname ^ "_" ^ string_of_id fid ^ ";"); hardline;
       space; space; space; string (" set_field = set_" ^ tname ^ "_" ^ string_of_id fid ^ " "); ranglebar])
  in
  separate_map hardline doc_field fields

let rec doc_def_lem def =
  (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
  match def with
  | DEF_spec v_spec -> doc_spec_lem v_spec
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def -> group (doc_typdef_lem t_def) ^/^ hardline
  | DEF_reg_dec dec -> group (doc_dec_lem dec)

  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef_lem fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec_lem fundefs ^/^ hardline
  | DEF_val (LB_aux (LB_val (pat, _), _) as lbind) ->
     group (doc_let_lem empty_ctxt lbind) ^/^ hardline
  | DEF_scattered sdef -> failwith "doc_def_lem: shoulnd't have DEF_scattered at this point"

  | DEF_kind _ -> empty

  | DEF_comm (DC_comm s) -> comment (string s)
  | DEF_comm (DC_comm_struct d) -> comment (doc_def_lem d)


let find_exc_typ defs =
  let is_exc_typ_def = function
    | DEF_type td -> string_of_id (id_of_type_def td) = "exception"
    | _ -> false in
  if List.exists is_exc_typ_def defs then "exception" else "unit"

let pp_defs_lem (types_file,types_modules) (defs_file,defs_modules) (Defs defs) top_line =
  (* let regtypes = find_regtypes d in *)
  let state_ids =
    State.generate_regstate_defs !opt_mwords defs
    |> Initial_check.val_spec_ids
  in
  let is_state_def = function
    | DEF_spec vs -> IdSet.mem (id_of_val_spec vs) state_ids
    | DEF_fundef fd -> IdSet.mem (id_of_fundef fd) state_ids
    | _ -> false
  in
  let is_typ_def = function
    | DEF_type _ -> true
    | _ -> false
  in
  let exc_typ = find_exc_typ defs in
  let typdefs, defs = List.partition is_typ_def defs in
  let statedefs, defs = List.partition is_state_def defs in
  let register_refs = State.register_refs_lem prefix_recordtype !opt_mwords (State.find_registers defs) in
  (print types_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "open import";string lib]) types_modules;hardline;
        if !print_to_from_interp_value
        then
          concat
            [(separate_map hardline)
               (fun lib -> separate space [string "     import";string lib]) ["Interp";"Interp_ast"];
             string "open import Deep_shallow_convert";
             hardline;
             hardline;
             string "module SI = Interp"; hardline;
             string "module SIA = Interp_ast"; hardline;
             hardline]
        else empty;
        separate empty (List.map doc_def_lem typdefs); hardline;
        hardline;
        separate empty (List.map doc_def_lem statedefs); hardline;
        hardline;
        register_refs; hardline;
        (* if !opt_sequential then
          concat [
            string ("type MR 'a 'r = State_monad.MR regstate 'a 'r " ^ exc_typ); hardline;
            string ("type M 'a = State_monad.M regstate 'a " ^ exc_typ); hardline;
          ]
        else *)
          concat [
            string ("type MR 'a 'r = monadR register_value 'a 'r " ^ exc_typ); hardline;
            string ("type M 'a = monad register_value 'a " ^ exc_typ); hardline
          ]
        ]);
  (print defs_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "open import";string lib]) defs_modules;hardline;
        hardline;
        separate empty (List.map doc_def_lem defs);
        hardline]);
