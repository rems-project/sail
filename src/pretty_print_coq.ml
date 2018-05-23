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

(* TODO:
  | DEF_reg_dec dec -> group (doc_dec_lem dec)
  | DEF_fundef fdef -> group (doc_fundef_lem fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec_lem fundefs ^/^ hardline

  doc_id / doc_id_type with a DeIid ...*
  fix_id
  doc_quant_item on constraints
  type quantifiers in records, unions
  update notation for records
  register_refs?
  should I control the nexps somewhat?
  L_real
  should P_var produce an "as"?
  does doc_pat detuple too much?
  Import ListNotations
  P_record?
  type quantifiers and constraints in definitions
  should atom types be specially treated?  (probably not in doc_typ, but elsewhere)
  ordering of kids in existential types is fragile!
  doc_nexp needs precedence fixed (i.e., parens inserted)
  doc_exp_lem assignments, foreach (etc), early_return (supress type when it's not ASTable?),
    application (do we need to bother printing types so much?), casts (probably ought to print type),
    record update
  lem/isabelle formatting hacks
  move List imports
  renaming kids bound in fn bodies as well as top-level funcl pattern
*)

open Type_check
open Ast
open Ast_util
open Rewriter
open PPrint
open Pretty_print_common

module StringSet = Set.Make(String)

(****************************************************************************
 * PPrint-based sail-to-coq pprinter
****************************************************************************)

type context = {
  early_ret : bool;
  kid_renames : kid KBindings.t; (* Plain tyvar -> tyvar renames *)
  kid_id_renames : id KBindings.t; (* tyvar -> argument renames *)
  bound_nexps : NexpSet.t;
}
let empty_ctxt = {
  early_ret = false;
  kid_renames = KBindings.empty;
  kid_id_renames = KBindings.empty;
  bound_nexps = NexpSet.empty
}

let langlebar = string "<|"
let ranglebar = string "|>"
let anglebars = enclose langlebar ranglebar
let enclose_record = enclose (string "{| ") (string " |}")
let bigarrow = string "=>"

let separate_opt s f l = separate s (Util.map_filter f l)

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

let doc_id (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_type (Id_aux(i,_)) =
  match i with
  | Id("int") -> string "Z"
  | Id("nat") -> string "Z"
  | Id i -> string (fix_id false i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     parens (separate space [colon; string x; empty])

let doc_id_ctor (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x ->
     (* add an extra space through empty to avoid a closing-comment
      * token in case of x ending with star. *)
     separate space [colon; string x; empty]

let doc_var_lem ctx kid =
  match KBindings.find kid ctx.kid_id_renames with
  | id -> doc_id id
  | exception Not_found ->
     string (fix_id true (string_of_kid (try KBindings.find kid ctx.kid_renames with Not_found -> kid)))

let doc_docstring_lem (l, _) = match l with
  | Parse_ast.Documented (str, _) -> string ("(*" ^ str ^ "*)") ^^ hardline
  | _ -> empty

let simple_annot l typ = (Parse_ast.Generated l, Some (Env.empty, typ, no_effect))
let simple_num l n = E_aux (
  E_lit (L_aux (L_num n, Parse_ast.Generated l)),
  simple_annot (Parse_ast.Generated l)
    (atom_typ (Nexp_aux (Nexp_constant n, Parse_ast.Generated l))))

let effectful_set = function
  | [] -> false
  | _ -> true
  (*List.exists
    (fun (BE_aux (eff,_)) ->
      match eff with
      | BE_rreg | BE_wreg | BE_rmem | BE_rmemt | BE_wmem | BE_eamem
      | BE_exmem | BE_wmv | BE_wmvt | BE_barr | BE_depend | BE_nondet
      | BE_escape -> true
      | _ -> false)*)

let effectful (Effect_aux (Effect_set effs, _)) = effectful_set effs

let is_regtyp (Typ_aux (typ, _)) env = match typ with
  | Typ_app(id, _) when string_of_id id = "register" -> true
  | _ -> false

let doc_nexp ctx nexp =
  let (Nexp_aux (nexp, l) as full_nexp) = nexp_simp nexp in
  match nexp with
  | Nexp_constant i -> string (Big_int.to_string i)
  | Nexp_var v -> doc_var_lem ctx v
  | Nexp_id id -> doc_id id
  | Nexp_times (n1, n2) -> separate space [doc_nexp n1; star; doc_nexp n2]
  | Nexp_sum (n1, n2) -> separate space [doc_nexp n1; plus; doc_nexp n2]
  | Nexp_minus (n1, n2) -> separate space [doc_nexp n1; minus; doc_nexp n2]
  | Nexp_exp n -> separate space [string "2"; caret; doc_nexp n]
  | Nexp_neg n -> separate space [minus; doc_nexp n]
  | _ ->
     raise (Reporting_basic.err_unreachable l
              ("cannot pretty-print nexp \"" ^ string_of_nexp full_nexp ^ "\"")) 

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
     if is_bit_typ elem_typ && not (is_nexp_constant m) then
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
let doc_typ, doc_atomic_typ =
  let fns ctx =
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
           | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
             string "mword " ^^ doc_nexp ctx (nexp_simp m)
           | _ -> string "list" ^^ space ^^ typ elem_typ in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
         let tpp = string "register_ref regstate register_value " ^^ typ etyp in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _),_) ->
         (string "Z")
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "Z")
      | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
         (string "Z")
      | Typ_app(id,args) ->
         let tpp = (doc_id_type id) ^^ space ^^ (separate_map space doc_typ_arg args) in
         if atyp_needed then parens tpp else tpp
      | _ -> atomic_typ atyp_needed ty
    and atomic_typ atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_id (Id_aux (Id "bool",_)) -> string "bool"
      | Typ_id (Id_aux (Id "bit",_)) -> string "bitU"
      | Typ_id (id) ->
         (*if List.exists ((=) (string_of_id id)) regtypes
         then string "register"
         else*) doc_id_type id
      | Typ_var v -> doc_var_lem ctx v
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ ty in
         if atyp_needed then parens tpp else tpp
      | Typ_exist (kids,_,ty) ->
         let tpp = typ ty in
tpp (*         List.fold_left
           (fun tpp kid -> braces (separate space [doc_var_lem kid; colon; string "Z"; ampersand; tpp]))
           tpp kids*)
    and doc_typ_arg (Typ_arg_aux(t,_)) = match t with
      | Typ_arg_typ t -> app_typ true t
      | Typ_arg_nexp n -> doc_nexp ctx n
      | Typ_arg_order o -> empty
  in typ', atomic_typ
  in (fun ctx -> (fst (fns ctx))), (fun ctx -> (snd (fns ctx)))

(* Check for variables in types that would be pretty-printed and are not
   bound in the val spec of the function. *)
let contains_t_pp_var ctxt (Typ_aux (t,a) as typ) =
  NexpSet.diff (lem_nexps_of_typ typ) ctxt.bound_nexps
  |> NexpSet.exists (fun nexp -> not (is_nexp_constant nexp))

let replace_typ_size ctxt env (Typ_aux (t,a)) =
  match t with
  | Typ_app (Id_aux (Id "vector",_) as id, [Typ_arg_aux (Typ_arg_nexp size,_);ord;typ']) ->
     begin
       let mk_typ nexp = 
         Some (Typ_aux (Typ_app (id, [Typ_arg_aux (Typ_arg_nexp nexp,Parse_ast.Unknown);ord;typ']),a))
       in
       match Type_check.solve env size with
       | Some n -> mk_typ (nconstant n)
       | None ->
          let is_equal nexp =
            prove env (NC_aux (NC_equal (size,nexp),Parse_ast.Unknown))
          in match List.find is_equal (NexpSet.elements ctxt.bound_nexps) with
          | nexp -> mk_typ nexp
          | exception Not_found -> None
     end
  | _ -> None

let doc_tannot_lem ctxt env eff typ =
  let of_typ typ =
    let ta = doc_typ ctxt typ in
    if eff then string " : M " ^^ parens ta
    else string " : " ^^ ta
  in
  if contains_t_pp_var ctxt typ
  then
    match replace_typ_size ctxt env typ with
    | None -> empty
    | Some typ -> of_typ typ
  else of_typ typ

let doc_lit (L_aux(lit,l)) =
  match lit with
  | L_unit  -> utf8string "tt"
  | L_zero  -> utf8string "B0"
  | L_one   -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i ->
     let ipp = Big_int.to_string i in
     utf8string ipp
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     utf8string "(return (failwith \"undefined value of unsupported type\"))"
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

(* TODO: parens *)
let rec doc_nc ctx (NC_aux (nc,_)) =
  match nc with
  | NC_equal (ne1, ne2) -> doc_op equals (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_bounded_ge (ne1, ne2) -> doc_op (string ">=") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_bounded_le (ne1, ne2) -> doc_op (string "<=") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_not_equal (ne1, ne2) -> doc_op (string "<>") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_set (kid, is) -> (* TODO: is this a good translation? *)
     separate space [string "In"; doc_var_lem ctx kid;
                     brackets (separate (string "; ")
                                 (List.map (fun i -> string (Nat_big_num.to_string i)) is))]
  | NC_or (nc1, nc2) -> doc_op (string "\\/") (doc_nc ctx nc1) (doc_nc ctx nc2)
  | NC_and (nc1, nc2) -> doc_op (string "/\\") (doc_nc ctx nc1) (doc_nc ctx nc2)
  | NC_true -> string "True"
  | NC_false -> string "False"

let doc_quant_item_id ctx delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_none kid,_)) ->
     if KBindings.mem kid ctx.kid_id_renames then None else
     Some (delimit (separate space [doc_var_lem ctx kid; colon; string "Z"]))
  | QI_id (KOpt_aux (KOpt_kind (K_aux (K_kind [BK_aux (kind,_)],_),kid),_)) -> begin
    if KBindings.mem kid ctx.kid_id_renames then None else
    match kind with
    | BK_type -> Some (delimit (separate space [doc_var_lem ctx kid; colon; string "Type"]))
    | BK_int -> Some (delimit (separate space [doc_var_lem ctx kid; colon; string "Z"]))
    | BK_order -> None
  end
  | QI_id _ -> failwith "Quantifier with multiple kinds"
  | QI_const nc -> None

let doc_quant_item_constr ctx delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id  _ -> None
  | QI_const nc -> Some (bquote ^^ braces (string "ArithFact" ^^ parens (doc_nc ctx nc)))

let doc_typquant_items ctx delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     separate_opt space (doc_quant_item_id ctx delimit) qis ^^
     separate_opt space (doc_quant_item_constr ctx delimit) qis
  | TypQ_no_forall -> empty

let doc_typquant_items_separate ctx delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     separate_opt space (doc_quant_item_id ctx delimit) qis,
     separate_opt space (doc_quant_item_constr ctx delimit) qis
  | TypQ_no_forall -> empty, empty

let doc_typquant ctx (TypQ_aux(tq,_)) typ = match tq with
| TypQ_tq ((_ :: _) as qs) ->
   string "forall " ^^ separate_opt space (doc_quant_item_id ctx parens) qs ^^
     separate_opt space (doc_quant_item_constr ctx parens) qs ^^ string ". " ^^ typ
| _ -> typ

(* Produce Size type constraints for bitvector sizes when using
   machine words.  Often these will be unnecessary, but this simple
   approach will do for now. *)

let rec typeclass_nexps (Typ_aux(t,_)) =
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

let doc_typschm ctx quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ ctx t in
  if quants then doc_typquant ctx tq pt else pt

let is_ctor env id = match Env.lookup_id id env with
| Enum _ -> true
| _ -> false

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat ctxt apat_needed (P_aux (p,(l,annot))) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_ctor id)
                       (parens (separate_map comma (doc_pat ctxt true) pats)) in
    if apat_needed then parens ppp else ppp
  | P_app(id, []) -> doc_id_ctor id
  | P_lit lit  -> doc_lit lit
  | P_wild -> underscore
  | P_id id -> doc_id id
  | P_var(p,_) -> doc_pat ctxt true p
  | P_as(p,id) -> parens (separate space [doc_pat ctxt true p; string "as"; doc_id id])
  | P_typ(typ,p) ->
    let doc_p = doc_pat ctxt true p in
    doc_p
    (* Type annotations aren't allowed everywhere in patterns in Coq *)
    (*parens (doc_op colon doc_p (doc_typ typ))*)
  | P_vector pats ->
     let ppp = brackets (separate_map semi (doc_pat ctxt true) pats) in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     raise (Reporting_basic.err_unreachable l
       "vector concatenation patterns should have been removed before pretty-printing")
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat ctxt apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat ctxt false) pats))
  | P_list pats -> brackets (separate_map semi (doc_pat ctxt false) pats)
  | P_cons (p,p') -> doc_op (string "::") (doc_pat ctxt true p) (doc_pat ctxt true p')
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

let find_e_ids exp =
  let e_id id = IdSet.singleton id, E_id id in
  fst (fold_exp
    { (compute_exp_alg IdSet.empty IdSet.union) with e_id = e_id } exp)

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
       (match le_act (*, t, tag*) with
        | LEXP_vector_range (le,e2,e3) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
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
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
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
            doc_id (typ_id_of (typ_of_annot lannot)) ^^
            underscore ^^
            doc_id id (*^^
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
       let epp = if_exp ctxt false c t e in
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
       | Id_aux (Id "None", _) as none -> doc_id_ctor none
       | Id_aux (Id "foreach", _) ->
          begin
            match args with
            | [exp1; exp2; exp3; ord_exp; vartuple; body] ->
               let loopvar, body = match body with
                 | E_aux (E_let (LB_aux (LB_val (
                     P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _), _), _), body), _) -> id, body
                 | E_aux (E_let (LB_aux (LB_val (
                     P_aux (P_var (P_aux (P_id id, _), _), _), _), _), body), _) -> id, body
                 | E_aux (E_let (LB_aux (LB_val (
                     P_aux (P_id id, _), _), _), body), _) -> id, body
                 | _ -> raise (Reporting_basic.err_unreachable l ("Unable to find loop variable in " ^ string_of_exp body)) in
               let step = match ord_exp with
                 | E_aux (E_lit (L_aux (L_false, _)), _) ->
                    parens (separate space [string "integerNegate"; expY exp3])
                 | _ -> expY exp3
               in
               let combinator = if effectful (effect_of body) then "foreachM" else "foreach" in
               let indices_pp = parens (separate space [string "index_list"; expY exp1; expY exp2; step]) in
               let used_vars_body = find_e_ids body in
               let body_lambda =
                 (* Work around indentation issues in Lem when translating
                    tuple or literal unit patterns to Isabelle *)
                 match fst (uncast_exp vartuple) with
                   | E_aux (E_tuple _, _)
                     when not (IdSet.mem (mk_id "varstup") used_vars_body)->
                      separate space [string "fun"; doc_id loopvar; string "varstup"; bigarrow]
                      ^^ break 1 ^^
                      separate space [string "let"; expY vartuple; string ":= varstup in"]
                   | E_aux (E_lit (L_aux (L_unit, _)), _)
                     when not (IdSet.mem (mk_id "unit_var") used_vars_body) ->
                      separate space [string "fun"; doc_id loopvar; string "unit_var"; bigarrow]
                   | _ ->
                      separate space [string "fun"; doc_id loopvar; expY vartuple; bigarrow]
               in
               parens (
                   (prefix 2 1)
                     ((separate space) [string combinator; indices_pp; expY vartuple])
                     (parens
                        (prefix 2 1 (group body_lambda) (expN body))
                     )
                 )
          | _ -> raise (Reporting_basic.err_unreachable l
             "Unexpected number of arguments for loop combinator")
          end
       | Id_aux (Id (("while" | "until") as combinator), _) ->
          begin
            match args with
            | [cond; varstuple; body] ->
               let return (E_aux (e, a)) = E_aux (E_internal_return (E_aux (e, a)), a) in
               let csuffix, cond, body =
                 match effectful (effect_of cond), effectful (effect_of body) with
                   | false, false -> "", cond, body
                   | false, true  -> "M", return cond, body
                   | true,  false -> "M", cond, return body
                   | true,  true  -> "M", cond, body
               in
               let used_vars_body = find_e_ids body in
               let lambda =
                 (* Work around indentation issues in Lem when translating
                    tuple or literal unit patterns to Isabelle *)
                 match fst (uncast_exp varstuple) with
                   | E_aux (E_tuple _, _)
                     when not (IdSet.mem (mk_id "varstup") used_vars_body)->
                      separate space [string "fun varstup"; bigarrow] ^^ break 1 ^^
                      separate space [string "let"; expY varstuple; string ":= varstup in"]
                   | E_aux (E_lit (L_aux (L_unit, _)), _)
                     when not (IdSet.mem (mk_id "unit_var") used_vars_body) ->
                      separate space [string "fun unit_var"; bigarrow]
                   | _ ->
                      separate space [string "fun"; expY varstuple; bigarrow]
               in
               parens (
                   (prefix 2 1)
                     ((separate space) [string (combinator ^ csuffix); expY varstuple])
                     ((prefix 0 1)
                       (parens (prefix 2 1 (group lambda) (expN cond)))
                       (parens (prefix 2 1 (group lambda) (expN body))))
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
                     doc_atomic_typ ctxt false (typ_of full_exp);
                     doc_atomic_typ ctxt false (typ_of exp)] in
                   true, doc_op colon epp tannot in
               if aexp_needed then parens tepp else tepp
            | _ -> raise (Reporting_basic.err_unreachable l
               "Unexpected number of arguments for early_return builtin")
          end
       | _ ->
          begin match annot with
          | Some (env, _, _) when Env.is_union_constructor f env ->
             let epp =
               match args with
               | [] -> doc_id_ctor f
               | [arg] -> doc_id_ctor f ^^ space ^^ expV true arg
               | _ ->
                  doc_id_ctor f ^^ space ^^ 
                    parens (separate_map comma (expV false) args) in
             if aexp_needed then parens (align epp) else epp
          | _ ->
             let call, is_extern = match annot with
               | Some (env, _, _) when Env.is_extern f env "coq" ->
                 string (Env.get_extern f env "coq"), true
               | _ -> doc_id f, false in
             let epp = hang 2 (flow (break 1) (call :: List.map expY args)) in
             let (taepp,aexp_needed) =
               let env = env_of full_exp in
               let t = Env.expand_synonyms env (typ_of full_exp) in
               let eff = effect_of full_exp in
               if typ_needs_printed t
               then (align (group (prefix 0 1 epp (doc_tannot_lem ctxt env (effectful eff) t))), true)
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
       (match fannot with
        | Some(env, (Typ_aux (Typ_id tid, _)), _)
        | Some(env, (Typ_aux (Typ_app (tid, _), _)), _)
          when Env.is_record tid env ->
           let fname =
             if prefix_recordtype && string_of_id tid <> "regstate"
             then (string (string_of_id tid ^ "_")) ^^ doc_id id
             else doc_id id in
           expY fexp ^^ dot ^^ fname
        | _ ->
           raise (report l "E_field expression with no register or record type"))
    | E_block [] -> string "tt"
    | E_block exps -> raise (report l "Blocks should have been removed till now.")
    | E_nondet exps -> raise (report l "Nondet blocks not supported.")
    | E_id id | E_ref id ->
       let env = env_of full_exp in
       let typ = typ_of full_exp in
       let eff = effect_of full_exp in
       let base_typ = Env.base_typ_of env typ in
       if has_effect eff BE_rreg then
         let epp = separate space [string "read_reg";doc_id (append_id id "_ref")] in
         if is_bitvector_typ base_typ
         then liftR (parens (align (group (prefix 0 1 epp (doc_tannot_lem ctxt env true base_typ)))))
         else liftR epp
       else if Env.is_register id env then doc_id (append_id id "_ref")
       else if is_ctor env id then doc_id_ctor id
       else doc_id id
    | E_lit lit -> doc_lit lit
    | E_cast(typ,e) ->
       expV aexp_needed e
    | E_tuple exps ->
       parens (align (group (separate_map (comma ^^ break 1) expN exps)))
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
       let recordtyp = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _) ->
           (* when Env.is_record tid env -> *)
           tid
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       let epp = enclose_record (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp ctxt recordtyp) fexps)) in
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
       let start, (len, order, etyp) =
         if is_vector_typ t then vector_start_index t, vector_typ_args_of t
         else raise (Reporting_basic.err_unreachable l
           "E_vector of non-vector type") in
       let dir,dir_out = if is_order_inc order then (true,"true") else (false, "false") in
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
         if is_bit_typ etyp then
           let bepp = string "vec_of_bits" ^^ space ^^ align epp in
           (align (group (prefix 0 1 bepp (doc_tannot_lem ctxt (env_of full_exp) false t))), true)
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
         let middle =
           match fst (untyp_pat pat) with
           | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
              string ">>"
           | P_aux (P_tup _, _)
             when not (IdSet.mem (mk_id "varstup") (find_e_ids e2)) ->
              (* Work around indentation issues in Lem when translating
                 tuple patterns to Isabelle *)
              separate space
                [string ">>= fun varstup => let";
                 doc_pat ctxt true pat;
                 string "= varstup in"]
           | _ ->
              separate space [string ">>= fun"; doc_pat ctxt true pat; bigarrow]
         in
         infix 0 1 middle (expV b e1) (expN e2)
       in
       if aexp_needed then parens (align epp) else epp
    | E_internal_return (e1) ->
       separate space [string "returnm"; expY e1]
    | E_sizeof nexp ->
      (match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit (L_aux (L_num i, l))
        | _ ->
          raise (Reporting_basic.err_unreachable l
            "pretty-printing non-constant sizeof expressions to Lem not supported"))
    | E_return r ->
      let ret_monad = " : MR" in
      let ta =
        if contains_t_pp_var ctxt (typ_of full_exp) || contains_t_pp_var ctxt (typ_of r)
        then empty
        else separate space
          [string ret_monad;
          parens (doc_typ ctxt (typ_of full_exp));
          parens (doc_typ ctxt (typ_of r))] in
      align (parens (string "early_return" ^//^ expV true r ^//^ ta))
    | E_constraint _ -> string "true"
    | E_comment _ | E_comment_struc _ -> empty
    | E_internal_cast _ | E_internal_exp _ | E_sizeof_internal _
    | E_internal_exp_user _ | E_internal_value _ ->
      raise (Reporting_basic.err_unreachable l
        "unsupported internal expression encountered while pretty-printing")
  and if_exp ctxt (elseif : bool) c t e =
    let if_pp = string (if elseif then "else if" else "if") in
    let else_pp = match e with
      | E_aux (E_if (c', t', e'), _)
      | E_aux (E_cast (_, E_aux (E_if (c', t', e'), _)), _) ->
         if_exp ctxt true c' t' e'
      | _ -> prefix 2 1 (string "else") (top_exp ctxt false e)
    in
    (prefix 2 1
      (soft_surround 2 1 if_pp (top_exp ctxt true c) (string "then"))
      (top_exp ctxt false t)) ^^
    break 1 ^^
    else_pp
  and let_exp ctxt (LB_aux(lb,_)) = match lb with
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true pat; coloneq])
              (top_exp ctxt false e)

  and doc_fexp ctxt recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype && string_of_id recordtyp <> "regstate"
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
      else doc_id id in
    group (doc_op coloneq fname (top_exp ctxt true e))

  and doc_case ctxt = function
  | Pat_aux(Pat_exp(pat,e),_) ->
    group (prefix 3 1 (separate space [pipe; doc_pat ctxt false pat;bigarrow])
                  (group (top_exp ctxt false e)))
  | Pat_aux(Pat_when(_,_,_),(l,_)) ->
    raise (Reporting_basic.err_unreachable l
      "guarded pattern expression should have been rewritten before pretty-printing")

  and doc_lexp_deref_lem ctxt ((LEXP_aux(lexp,(l,annot)))) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref_lem ctxt le;dot;doc_id id])
    | LEXP_id id -> doc_id (append_id id "_ref")
    | LEXP_cast (typ,id) -> doc_id (append_id id "_ref")
    | LEXP_tup lexps -> parens (separate_map comma_sp (doc_lexp_deref_lem ctxt) lexps)
    | _ ->
       raise (Reporting_basic.err_unreachable l ("doc_lexp_deref_lem: Unsupported lexp"))
             (* expose doc_exp_lem and doc_let *)
  in top_exp, let_exp

let doc_type_union ctxt typ_name (Tu_aux(Tu_ty_id(typ,id),_)) =
  separate space [doc_id_ctor id; colon;
                  doc_typ ctxt typ; arrow; typ_name]

let rec doc_range_lem (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef (TD_aux(td, (l, annot))) = match td with
  | TD_abbrev(id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     doc_op coloneq
       (separate space [string "Definition"; doc_id_type id; doc_typquant_items empty_ctxt parens typq])
       (doc_typschm empty_ctxt false typschm) ^^ dot
  | TD_record(id,nm,typq,fs,_) ->
    let fname fid = if prefix_recordtype && string_of_id id <> "regstate"
                    then concat [doc_id id;string "_";doc_id_type fid;]
                    else doc_id_type fid in
    let f_pp (typ,fid) =
      concat [fname fid;space;colon;space;doc_typ empty_ctxt typ; semi] in
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
    let doc_update_field (_,fid) =
      let idpp = fname fid in
      let otherfield (_,fid') =
        if Id.compare fid fid' == 0 then empty else
          let idpp = fname fid' in
          separate space [semi; idpp; string ":="; idpp; string "r"]
      in
      string "Notation \"{[ r 'with' '" ^^ idpp ^^ string "' := e ]}\" := ({| " ^^
        idpp ^^ string " := e" ^^ concat (List.map otherfield fs) ^^
        space ^^ string "|})."
    in
    let updates_pp = separate hardline (List.map doc_update_field fs) in
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
          let start, (_, ord, _) = vector_start_index base_ftyp, vector_typ_args_of base_ftyp in
          match nexp_simp start with
          | Nexp_aux (Nexp_constant i, _) -> (i, is_order_inc ord)
          | _ ->
            raise (Reporting_basic.err_unreachable Parse_ast.Unknown
              ("register " ^ string_of_id id ^ " has non-constant start index " ^ string_of_nexp start))
        with
        | _ -> (Big_int.zero, true) in
      doc_op equals
        (concat [string "let "; parens (concat [doc_id id; underscore; doc_id fid; rfannot])])
        (anglebars (concat [space;
          doc_op equals (string "field_name") (string_lit (doc_id fid)); semi_sp;
          doc_op equals (string "field_start") (string (Big_int.to_string start)); semi_sp;
          doc_op equals (string "field_is_inc") (string (if is_inc then "true" else "false")); semi_sp;
          doc_op equals (string "get_field") (parens (doc_op arrow (string "fun rec_val") get)); semi_sp;
          doc_op equals (string "set_field") (parens (doc_op arrow (string "fun rec_val v") set)); space])) in *)
    doc_op coloneq
           (separate space [string "Record"; doc_id_type id; doc_typquant_items empty_ctxt parens typq])
           ((*doc_typquant_lem typq*) (braces (space ^^ align fs_doc ^^ space))) ^^
      dot ^^ hardline ^^ updates_pp
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
         let typ_nm = separate space [doc_id_type id; doc_typquant_items empty_ctxt parens typq] in
         let ar_doc = group (separate_map (break 1 ^^ pipe ^^ space) (doc_type_union empty_ctxt typ_nm) ar) in
         let typ_pp =
           (doc_op coloneq)
             (concat [string "Inductive"; space; typ_nm])
             ((*doc_typquant_lem typq*) ar_doc) in
         typ_pp ^^ dot ^^ hardline ^^ hardline)
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
         let enums_doc = group (separate_map (break 1 ^^ pipe ^^ space) doc_id_ctor enums) in
         let typ_pp = (doc_op coloneq)
                        (concat [string "Inductive"; space; doc_id_type id;])
                        (enums_doc) in
          typ_pp ^^ dot ^^ hardline ^^ hardline)
    | _ -> raise (Reporting_basic.err_unreachable l "register with non-constant indices")

let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    (P_aux (P_id id, (l, Some (env, typ, no_effect))), typ),
    E_aux (E_id id, (l, Some (env, typ, no_effect))) in
  List.split (List.mapi arg typs)

let rec untuple_args_pat typ (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let tup_typs = match typ with
    | Typ_aux (Typ_tup typs, _) -> Some typs
    | _ -> match Env.expand_synonyms env typ with
      | Typ_aux (Typ_tup typs, _) -> Some typs
      | _ -> None
  in
  let identity = (fun body -> body) in
  match paux, tup_typs with
  | P_tup [], _ ->
     let annot = (l, Some (Env.empty, unit_typ, no_effect)) in
     [P_aux (P_lit (mk_lit L_unit), annot), unit_typ], identity
  | P_tup pats, Some typs -> List.combine pats typs, identity
  | P_tup pats, _ -> failwith "Tuple pattern against non-tuple type"
  | P_wild, Some typs ->
     let wild typ = P_aux (P_wild, (l, Some (env, typ, no_effect))), typ in
     List.map wild typs, identity
  | P_typ (_, pat), _ -> untuple_args_pat typ pat
  | P_as _, Some typs | P_id _, Some typs ->
     let argpats, argexps = args_of_typ l env typs in
     let argexp = E_aux (E_tuple argexps, annot) in
     let bindargs (E_aux (_, bannot) as body) =
       E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
     argpats, bindargs
  | _, _ ->
     [pat,typ], identity

let doc_rec (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> string "Definition"
  | Rec_rec -> string "Fixpoint"

let doc_fun_body ctxt exp =
  let doc_exp = doc_exp_lem ctxt false exp in
  if ctxt.early_ret
  then align (string "catch_early_return" ^//^ parens (doc_exp))
  else doc_exp

(* Coq doesn't support "as" patterns well in Definition binders, so we push
   them over to the r.h.s. of the := *)
let demote_as_pattern i (P_aux (_,p_annot) as pat,typ) =
  let open Rewriter in
  if fst (fold_pat ({ (compute_pat_alg false (||)) with p_as = (fun ((_,p),id) -> true, P_as (p,id)) }) pat)
  then
    let id = mk_id ("arg" ^ string_of_int i) in (* TODO: name conflicts *)
    (P_aux (P_id id, p_annot),typ),
    fun (E_aux (_,e_ann) as e) ->
      E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)
  else (pat,typ), fun e -> e

(* Ideally we'd remove the duplication between type variables and atom
   arguments, but for now we just add an equality constraint. *)

let atom_constraint ctxt (pat, typ) =
  let typ = Env.base_typ_of (pat_env_of pat) typ in
  match pat, typ with
  | P_aux (P_id id, _),
      Typ_aux (Typ_app (Id_aux (Id "atom",_),
                        [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid,_)),_)]),_) ->
     Some (bquote ^^ braces (string "ArithFact" ^^ space ^^
                               parens (doc_op equals (doc_id id) (doc_var_lem ctxt kid))))
  | _ -> None

let all_ids pexp =
  let open Rewriter in
  fold_pexp (
    { (pure_exp_alg IdSet.empty IdSet.union) with
      e_id = (fun id -> IdSet.singleton id);
      e_ref = (fun id -> IdSet.singleton id);
      e_app = (fun (id,ids) ->
        List.fold_left IdSet.union (IdSet.singleton id) ids);
      e_app_infix = (fun (ids1,id,ids2) ->
        IdSet.add id (IdSet.union ids1 ids2));
      e_for = (fun (id,ids1,ids2,ids3,_,ids4) ->
        IdSet.add id (IdSet.union ids1 (IdSet.union ids2 (IdSet.union ids3 ids4))));
      lEXP_id = IdSet.singleton;
      lEXP_memory = (fun (id,ids) ->
        List.fold_left IdSet.union (IdSet.singleton id) ids);
      lEXP_cast = (fun (_,id) -> IdSet.singleton id);
      pat_alg = { (pure_pat_alg IdSet.empty IdSet.union) with
        p_as = (fun (ids,id) -> IdSet.add id ids);
        p_id = IdSet.singleton;
        p_app = (fun (id,ids) ->
          List.fold_left IdSet.union (IdSet.singleton id) ids);
      }
    }) pexp

let tyvars_of_typquant (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_no_forall -> KidSet.empty
  | TypQ_tq qs -> List.fold_left KidSet.union KidSet.empty
     (List.map tyvars_of_quant_item qs)

let mk_kid_renames ids_to_avoid kids =
  let map_id = function
    | Id_aux (Id i, _) -> Some (fix_id false i)
    | Id_aux (DeIid _, _) -> None
  in
  let ids = StringSet.of_list (Util.map_filter map_id (IdSet.elements ids_to_avoid)) in
  let rec check_kid kid (newkids,rebindings) =
    let rec check kid1 =
      let kid_string = fix_id true (string_of_kid kid1) in
      if StringSet.mem kid_string ids
      then let kid2 = match kid1 with Kid_aux (Var x,l) -> Kid_aux (Var (x ^ "0"),l) in
           check kid2
      else
        KidSet.add kid1 newkids, KBindings.add kid kid1 rebindings
    in check kid
  in snd (KidSet.fold check_kid kids (kids, KBindings.empty))

let merge_kids_atoms pats =
  let try_eliminate (gone,map,seen) = function
    | P_aux (P_id id, ann), typ -> begin
      match Type_check.destruct_atom_nexp (env_of_annot ann) typ with
      | Some (Nexp_aux (Nexp_var kid,l)) ->
         if KidSet.mem kid seen then
           let () = 
             Reporting_basic.print_err false true l "merge_kids_atoms"
               ("want to merge tyvar and argument for " ^ string_of_kid kid ^
                   " but rearranging arguments isn't supported yet") in
           gone,map,seen
         else
           KidSet.add kid gone, KBindings.add kid id map, KidSet.add kid seen
      | _ -> gone,map,KidSet.union seen (tyvars_of_typ typ)
    end
    | _, typ -> gone,map,KidSet.union seen (tyvars_of_typ typ)
  in
  let gone,map,_ = List.fold_left try_eliminate (KidSet.empty, KBindings.empty, KidSet.empty) pats in
  gone,map

let doc_funcl (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let (tq,typ) = Env.get_val_spec_orig id (env_of_annot annot) in
  let (arg_typ, ret_typ, eff) = match typ with
    | Typ_aux (Typ_fn (arg_typ, ret_typ, eff),_) -> arg_typ, ret_typ, eff
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let ids_to_avoid = all_ids pexp in
  let kids_used = tyvars_of_typquant tq in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let pats, bind = untuple_args_pat arg_typ pat in
  let pats, binds = List.split (Util.list_mapi demote_as_pattern pats) in
  let eliminated_kids, kid_to_arg_rename = merge_kids_atoms pats in
  let kids_used = KidSet.diff kids_used eliminated_kids in
  let ctxt =
    { early_ret = contains_early_return exp;
      kid_renames = mk_kid_renames ids_to_avoid kids_used;
      kid_id_renames = kid_to_arg_rename;
      bound_nexps = NexpSet.union (lem_nexps_of_typ typ) (typeclass_nexps typ) } in
  (* Put the constraints after pattern matching so that any type variable that's
     been replaced by one of the term-level arguments is bound. *)
  let quantspp, constrspp = doc_typquant_items_separate ctxt braces tq in
  let exp = List.fold_left (fun body f -> f body) (bind exp) binds in
  let patspp = separate_map space (fun (pat,typ) ->
    squote ^^ parens (separate space [doc_pat ctxt true pat; colon; doc_typ ctxt typ])) pats in
  let atom_constr_pp = separate_opt space (atom_constraint ctxt) pats in
  let retpp =
    if effectful eff
    then string "M" ^^ space ^^ parens (doc_typ ctxt ret_typ)
    else doc_typ ctxt ret_typ
  in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting_basic.err_unreachable l
                "guarded pattern expression should have been rewritten before pretty-printing") in
  group (prefix 3 1
    (separate space [doc_id id; quantspp; patspp; constrspp; atom_constr_pp; colon; retpp; coloneq])
    (doc_fun_body ctxt exp ^^ dot))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_),_))::_ -> id

(* Strictly speaking, Lem doesn't support multiple clauses for a single function
   joined by "and", although it has worked for Isabelle before.  However, all
   the funcls should have been merged by the merge_funcls rewrite now. *)   
let doc_fundef_rhs_lem (FD_aux(FD_function(r, typa, efa, funcls),fannot)) =
  separate_map (hardline ^^ string "and ") doc_funcl funcls

let doc_mutrec_lem = function
  | [] -> failwith "DEF_internal_mutrec with empty function list"
  | fundefs ->
     string "let rec " ^^
     separate_map (hardline ^^ string "and ") doc_fundef_rhs_lem fundefs

let rec doc_fundef (FD_aux(FD_function(r, typa, efa, fcls),fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,_),annot) as funcl]
    when not (Env.is_extern id (env_of_annot annot) "coq") ->
    (doc_rec r) ^^ space ^^ (doc_funcl funcl)
  | [_] -> empty (* extern *)
  | _ -> failwith "FD_function with more than one clause"



let doc_dec_lem (DEC_aux (reg, ((l, _) as annot))) =
  match reg with
  | DEC_reg(typ,id) -> empty
     (*
       let env = env_of_annot annot in
       let rt = Env.base_typ_of env typ in
       if is_vector_typ rt then
         let start, (size, order, etyp) = vector_start_index rt, vector_typ_args_of rt in
         if is_bit_typ etyp && is_nexp_constant start && is_nexp_constant size then
           let o = if is_order_inc order then "true" else "false" in
           (doc_op equals)
             (string "let" ^^ space ^^ doc_id id)
             (string "Register" ^^ space ^^
                align (separate space [string_lit(doc_id id);
                                       doc_nexp (size);
                                       doc_nexp (start);
                                       string o;
                                       string "[]"]))
           ^/^ hardline
         else raise (Reporting_basic.err_unreachable l ("can't deal with register type " ^ string_of_typ typ))
       else raise (Reporting_basic.err_unreachable l ("can't deal with register type " ^ string_of_typ typ)) *)
  | DEC_alias(id,alspec) -> empty
  | DEC_typ_alias(typ,id,alspec) -> empty

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
     (concat [string "let "; parens (concat [string tname; underscore; doc_id fid; rfannot])])
     (concat [
       space; langlebar; string " field_name = \"" ^^ doc_id fid ^^ string "\";"; hardline;
       space; space; space; string (" field_start = " ^ Big_int.to_string i ^ ";"); hardline;
       space; space; space; string (" field_is_inc = " ^ dir ^ ";"); hardline;
       space; space; space; string (" get_field = get_" ^ tname ^ "_" ^ string_of_id fid ^ ";"); hardline;
       space; space; space; string (" set_field = set_" ^ tname ^ "_" ^ string_of_id fid ^ " "); ranglebar])
  in
  separate_map hardline doc_field fields

let rec doc_def def =
  (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
  match def with
  | DEF_spec v_spec -> empty (* Types appear in definitions *)
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def -> group (doc_typdef t_def) ^/^ hardline
  | DEF_reg_dec dec -> group (doc_dec_lem dec)

  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec_lem fundefs ^/^ hardline
  | DEF_val (LB_aux (LB_val (pat, exp), _)) ->
     let (id,typpp) = match pat with
       | P_aux (P_typ (typ, P_aux (P_id id,_)),_) -> id, space ^^ colon ^^ space ^^ doc_typ empty_ctxt typ
       | P_aux (P_id id, _) -> id, empty
       | _ -> failwith "Top-level value definition with complex pattern not supported for Coq yet"
     in
     group (string "Definition" ^^ space ^^ doc_id id ^^ typpp ^^ space ^^ coloneq ^^
              doc_exp_lem empty_ctxt false exp ^^ dot) ^/^ hardline
  | DEF_scattered sdef -> failwith "doc_def: shoulnd't have DEF_scattered at this point"

  | DEF_kind _ -> empty

  | DEF_comm (DC_comm s) -> comment (string s)
  | DEF_comm (DC_comm_struct d) -> comment (doc_def d)


let find_exc_typ defs =
  let is_exc_typ_def = function
    | DEF_type td -> string_of_id (id_of_type_def td) = "exception"
    | _ -> false in
  if List.exists is_exc_typ_def defs then "exception" else "unit"

let pp_defs_coq (types_file,types_modules) (defs_file,defs_modules) (Defs defs) top_line =
  (* let regtypes = find_regtypes d in *)
  let state_ids =
    State.generate_regstate_defs true defs
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
  let register_refs = State.register_refs_coq (State.find_registers defs) in
  (print types_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) types_modules;hardline;
string "Require Import String."; hardline;
        separate empty (List.map doc_def typdefs); hardline;
        hardline;
        separate empty (List.map doc_def statedefs); hardline;
        hardline;
        register_refs; hardline;
        concat [
          string ("Definition MR a r := monadR register_value a r " ^ exc_typ ^ "."); hardline;
          string ("Definition M a := monad register_value a " ^ exc_typ ^ "."); hardline
        ]
        ]);
  (print defs_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) defs_modules;hardline;
string "Require Import List. Import ListNotations.";
        hardline;
        separate empty (List.map doc_def defs);
        hardline]);
