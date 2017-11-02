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
(*    Thomas Bauereiss                                                    *)
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
open Big_int
open PPrint
open Pretty_print_common

(****************************************************************************
 * PPrint-based sail-to-lem pprinter
****************************************************************************)

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

let effectful (Effect_aux (eff,_)) =
  match eff with
  | Effect_var _ -> failwith "effectful: Effect_var not supported"
  | Effect_set effs -> effectful_set effs

let is_regtyp (Typ_aux (typ, _)) env = match typ with
  | Typ_app(id, _) when string_of_id id = "register" -> true
  | Typ_id(id) when Env.is_regtyp id env -> true
  | _ -> false

let doc_nexp_lem nexp =
  let (Nexp_aux (nexp, l) as full_nexp) = nexp_simp nexp in
  match nexp with
  | Nexp_constant i -> string ("ty" ^ string_of_int i)
  | Nexp_var v -> string (string_of_kid (orig_kid v))
  | _ ->
     let rec mangle_nexp (Nexp_aux (nexp, _)) = begin
       match nexp with
       | Nexp_id id -> string_of_id id
       | Nexp_var kid -> string_of_id (id_of_kid (orig_kid kid))
       | Nexp_constant i -> Pretty_print_lem_ast.lemnum string_of_int i
       | Nexp_times (n1, n2) -> mangle_nexp n1 ^ "_times_" ^ mangle_nexp n2
       | Nexp_sum (n1, n2) -> mangle_nexp n1 ^ "_plus_" ^ mangle_nexp n2
       | Nexp_minus (n1, n2) -> mangle_nexp n1 ^ "_minus_" ^ mangle_nexp n2
       | Nexp_exp n -> "exp_" ^ mangle_nexp n
       | Nexp_neg n -> "neg_" ^ mangle_nexp n
     end in
     string ("'" ^ mangle_nexp full_nexp)
     (* raise (Reporting_basic.err_unreachable l
       ("cannot pretty-print non-atomic nexp \"" ^ string_of_nexp full_nexp ^ "\"")) *)

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
let rec lem_nexps_of_typ sequential mwords (Typ_aux (t,_)) =
  let trec = lem_nexps_of_typ sequential mwords in
  match t with
  | Typ_wild
  | Typ_id _ -> NexpSet.empty
  | Typ_var kid -> NexpSet.singleton (orig_nexp (nvar kid))
  | Typ_fn (t1,t2,_) -> NexpSet.union (trec t1) (trec t2)
  | Typ_tup ts ->
     List.fold_left (fun s t -> NexpSet.union s (trec t))
       NexpSet.empty ts
  | Typ_app(Id_aux (Id "vector", _), [
    Typ_arg_aux (Typ_arg_nexp n, _);
    Typ_arg_aux (Typ_arg_nexp m, _);
    Typ_arg_aux (Typ_arg_order ord, _);
    Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
     let m = nexp_simp m in
     if mwords && is_bit_typ elem_typ && not (is_nexp_constant m) then
       NexpSet.singleton (orig_nexp m)
     else trec elem_typ
     (* NexpSet.union
       (if mwords then tyvars_of_nexp (nexp_simp m) else NexpSet.empty)
       (trec elem_typ) *)
  | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
     if sequential then trec etyp else NexpSet.empty
  | Typ_app(Id_aux (Id "range", _),_)
  | Typ_app(Id_aux (Id "implicit", _),_)
  | Typ_app(Id_aux (Id "atom", _), _) -> NexpSet.empty
  | Typ_app (_,tas) ->
     List.fold_left (fun s ta -> NexpSet.union s (lem_nexps_of_typ_arg sequential mwords ta))
       NexpSet.empty tas
  | Typ_exist (kids,_,t) ->
     let s = trec t in
     List.fold_left (fun s k -> NexpSet.remove k s) s (List.map nvar kids)
and lem_nexps_of_typ_arg sequential mwords (Typ_arg_aux (ta,_)) =
  match ta with
  | Typ_arg_nexp nexp -> NexpSet.singleton (nexp_simp (orig_nexp nexp))
  | Typ_arg_typ typ -> lem_nexps_of_typ sequential mwords typ
  | Typ_arg_order _ -> NexpSet.empty

let lem_tyvars_of_typ sequential mwords typ =
  NexpSet.fold (fun nexp ks -> KidSet.union ks (tyvars_of_nexp nexp))
    (lem_nexps_of_typ sequential mwords typ) KidSet.empty

(* When making changes here, check whether they affect lem_tyvars_of_typ *)
let doc_typ_lem, doc_atomic_typ_lem =
  (* following the structure of parser for precedence *)
  let rec typ sequential mwords ty = fn_typ sequential mwords true ty
    and typ' sequential mwords ty = fn_typ sequential mwords false ty
    and fn_typ (sequential : bool) (mwords : bool) atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_fn(arg,ret,efct) ->
         (*let exc_typ = string "string" in*)
         let ret_typ =
           if effectful efct
           then separate space [string "_M";(*parens exc_typ;*) fn_typ sequential mwords true ret]
           else separate space [fn_typ sequential mwords false ret] in
         let tpp = separate space [tup_typ sequential mwords true arg; arrow;ret_typ] in
         (* once we have proper excetions we need to know what the exceptions type is *)
         if atyp_needed then parens tpp else tpp
      | _ -> tup_typ sequential mwords atyp_needed ty
    and tup_typ sequential mwords atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_tup typs ->
         let tpp = separate_map (space ^^ star ^^ space) (app_typ sequential mwords false) typs in
         if atyp_needed then parens tpp else tpp
      | _ -> app_typ sequential mwords atyp_needed ty
    and app_typ sequential mwords atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_app(Id_aux (Id "vector", _), [
          Typ_arg_aux (Typ_arg_nexp n, _);
          Typ_arg_aux (Typ_arg_nexp m, _);
          Typ_arg_aux (Typ_arg_order ord, _);
          Typ_arg_aux (Typ_arg_typ elem_typ, _)]) ->
         let tpp = match elem_typ with
           | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) when mwords ->
             string "bitvector " ^^ doc_nexp_lem (nexp_simp m)
             (* (match nexp_simp m with
               | (Nexp_aux(Nexp_constant i,_)) -> string "bitvector ty" ^^ doc_int i
               | (Nexp_aux(Nexp_var _, _)) -> separate space [string "bitvector"; doc_nexp m]
               | _ -> raise (Reporting_basic.err_unreachable l
                 "cannot pretty-print bitvector type with non-constant length")) *)
           | _ -> string "vector" ^^ space ^^ typ sequential mwords elem_typ in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
         (* TODO: Better distinguish register names and contents? *)
         (* fn_typ regtypes atyp_needed etyp *)
         let tpp =
           if sequential
           then string "register_ref regstate " ^^ typ sequential mwords etyp
           else string "register" in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "integer")
      | Typ_app(Id_aux (Id "atom", _), [Typ_arg_aux(Typ_arg_nexp n,_)]) ->
         (string "integer")
      | Typ_app(id,args) ->
         let tpp = (doc_id_lem_type id) ^^ space ^^ (separate_map space (doc_typ_arg_lem sequential mwords) args) in
         if atyp_needed then parens tpp else tpp
      | _ -> atomic_typ sequential mwords atyp_needed ty
    and atomic_typ sequential mwords atyp_needed ((Typ_aux (t, l)) as ty) = match t with
      | Typ_id (Id_aux (Id "bool",_)) -> string "bool"
      | Typ_id (Id_aux (Id "bit",_)) -> string "bitU"
      | Typ_id (id) ->
         (*if List.exists ((=) (string_of_id id)) regtypes
         then string "register"
         else*) doc_id_lem_type id
      | Typ_var v -> doc_var v
      | Typ_wild -> underscore
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ sequential mwords ty in
         if atyp_needed then parens tpp else tpp
      | Typ_exist (kids,_,ty) -> begin
         let tpp = typ sequential mwords ty in
         let visible_vars = lem_tyvars_of_typ sequential mwords ty in
         match List.filter (fun kid -> KidSet.mem kid visible_vars) kids with
         | [] -> if atyp_needed then parens tpp else tpp
         | bad -> raise (Reporting_basic.err_general l
                           ("Existential type variable(s) " ^
                               String.concat ", " (List.map string_of_kid bad) ^
                               " escape into Lem"))
      end
    and doc_typ_arg_lem sequential mwords (Typ_arg_aux(t,_)) = match t with
      | Typ_arg_typ t -> app_typ sequential mwords true t
      | Typ_arg_nexp n -> doc_nexp_lem (nexp_simp n)
      | Typ_arg_order o -> empty
  in typ', atomic_typ


(* Check for variables in types that would be pretty-printed.
   In particular, in case of vector types, only the element type and the
   length argument are checked for variables, and the latter only if it is
   a bitvector; for other types of vectors, the length is not pretty-printed
   in the type, and the start index is never pretty-printed in vector types. *)
let rec contains_t_pp_var (Typ_aux (t,a) as typ) = match t with
  | Typ_wild -> true
  | Typ_id _ -> false
  | Typ_var _ -> true
  | Typ_exist _ -> true
  | Typ_fn (t1,t2,_) -> contains_t_pp_var t1 || contains_t_pp_var t2
  | Typ_tup ts -> List.exists contains_t_pp_var ts
  | Typ_app (c,targs) ->
      if Ast_util.is_number typ then false
      else if is_bitvector_typ typ then
        let (_,length,_,_) = vector_typ_args_of typ in
        not (is_nexp_constant (nexp_simp length))
      else List.exists contains_t_arg_pp_var targs
and contains_t_arg_pp_var (Typ_arg_aux (targ, _)) = match targ with
  | Typ_arg_typ t -> contains_t_pp_var t
  | Typ_arg_nexp nexp -> not (is_nexp_constant (nexp_simp nexp))
  | _ -> false

let doc_tannot_lem sequential mwords eff typ =
  if contains_t_pp_var typ then empty
  else
    let ta = doc_typ_lem sequential mwords typ in
    if eff then string " : _M " ^^ parens ta
    else string " : " ^^ ta

(* doc_lit_lem gets as an additional parameter the type information from the
 * expression around it: that's a hack, but how else can we distinguish between
 * undefined values of different types ? *)
let doc_lit_lem sequential mwords in_pat (L_aux(lit,l)) a =
  match lit with
  | L_unit  -> utf8string "()"
  | L_zero  -> utf8string "B0"
  | L_one   -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i ->
     let ipp = string_of_int i in
     utf8string (
       if in_pat then "("^ipp^":nn)"
       else if i < 0 then "((0"^ipp^"):ii)"
       else "("^ipp^":ii)")
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     (match a with
       | Some (_, (Typ_aux (t,_) as typ), _) ->
         (match t with
          | Typ_id (Id_aux (Id "bit", _))
          | Typ_app (Id_aux (Id "register", _),_) -> utf8string "UndefinedRegister 0"
          | Typ_id (Id_aux (Id "string", _)) -> utf8string "\"\""
          | _ ->
            let ta = if contains_t_pp_var typ then empty else doc_tannot_lem sequential mwords false typ in
            parens
              ((utf8string "(failwith \"undefined value of unsupported type\")") ^^ ta))
       | _ -> utf8string "(failwith \"undefined value of unsupported type\")")
  | L_string s -> utf8string ("\"" ^ s ^ "\"")
  | L_real s ->
    (* Lem does not support decimal syntax, so we translate a string
       of the form "x.y" into the ratio (x * 10^len(y) + y) / 10^len(y).
       The OCaml library has a conversion function from strings to floats, but
       not from floats to ratios. ZArith's Q library does have the latter, but
       using this would require adding a dependency on ZArith to Sail. *)
    let parts = Util.split_on_char '.' s in
    let (num, denom) = match parts with
    | [i] -> (big_int_of_string i, unit_big_int)
    | [i;f] ->
      let denom = power_int_positive_int 10 (String.length f) in
      (add_big_int (mult_big_int (big_int_of_string i) denom) (big_int_of_string f), denom)
    | _ ->
      raise (Reporting_basic.Fatal_error
        (Reporting_basic.Err_syntax_locn (l, "could not parse real literal"))) in
    separate space (List.map string ["realFromFrac"; string_of_big_int num; string_of_big_int denom])

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

let rec typeclass_nexps (Typ_aux(t,_)) = match t with
| Typ_wild
| Typ_id _
| Typ_var _
  -> NexpSet.empty
| Typ_fn (t1,t2,_) -> NexpSet.union (typeclass_nexps t1) (typeclass_nexps t2)
| Typ_tup ts -> List.fold_left NexpSet.union NexpSet.empty (List.map typeclass_nexps ts)
| Typ_app (Id_aux (Id "vector",_),
           [_;Typ_arg_aux (Typ_arg_nexp size_nexp,_);
            _;Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)])
| Typ_app (Id_aux (Id "itself",_),
           [Typ_arg_aux (Typ_arg_nexp size_nexp,_)]) ->
   let size_nexp = nexp_simp size_nexp in
   if is_nexp_constant size_nexp then NexpSet.empty else
   NexpSet.singleton (orig_nexp size_nexp)
| Typ_app _ -> NexpSet.empty
| Typ_exist (kids,_,t) -> NexpSet.empty (* todo *)

let doc_typclasses_lem mwords t =
  if mwords then
    let nexps = typeclass_nexps t in
    if NexpSet.is_empty nexps then (empty, NexpSet.empty) else
    (separate_map comma_sp (fun nexp -> string "Size " ^^ doc_nexp_lem nexp) (NexpSet.elements nexps) ^^ string " => ", nexps)
  else (empty, NexpSet.empty)

let doc_typschm_lem sequential mwords quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ_lem sequential mwords t in
  if quants
  then
    let nexps_used = lem_nexps_of_typ sequential mwords t in
    let ptyc, nexps_sizes = doc_typclasses_lem mwords t in
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
let rec doc_pat_lem sequential mwords apat_needed (P_aux (p,(l,annot)) as pa) = match p with
  | P_app(id, ((_ :: _) as pats)) ->
    let ppp = doc_unop (doc_id_lem_ctor id)
                       (parens (separate_map comma (doc_pat_lem sequential mwords true) pats)) in
    if apat_needed then parens ppp else ppp
  | P_app(id,[]) -> doc_id_lem_ctor id
  | P_lit lit  -> doc_lit_lem sequential mwords true lit annot
  | P_wild -> underscore
  | P_id id ->
     begin match id with
     | Id_aux (Id "None",_) -> string "Nothing" (* workaround temporary issue *)
     | _ -> doc_id_lem id end
  | P_var(p,kid) -> doc_pat_lem sequential mwords true p
  | P_as(p,id) -> parens (separate space [doc_pat_lem sequential mwords true p; string "as"; doc_id_lem id])
  | P_typ(typ,p) ->
    let doc_p = doc_pat_lem sequential mwords true p in
    if contains_t_pp_var typ then doc_p
    else parens (doc_op colon doc_p (doc_typ_lem sequential mwords typ))
  | P_vector pats ->
     let ppp =
       (separate space)
         [string "Vector";brackets (separate_map semi (doc_pat_lem sequential mwords true) pats);underscore;underscore] in
     if apat_needed then parens ppp else ppp
  | P_vector_concat pats ->
     raise (Reporting_basic.err_unreachable l
       "vector concatenation patterns should have been removed before pretty-printing")
  | P_tup pats  ->
     (match pats with
      | [p] -> doc_pat_lem sequential mwords apat_needed p
      | _ -> parens (separate_map comma_sp (doc_pat_lem sequential mwords false) pats))
  | P_list pats -> brackets (separate_map semi (doc_pat_lem sequential mwords false) pats) (*Never seen but easy in lem*)
  | P_cons (p,p') -> doc_op (string "::") (doc_pat_lem sequential mwords true p) (doc_pat_lem sequential mwords true p')
  | P_record (_,_) -> empty (* TODO *)

let rec typ_needs_printed (Typ_aux (t,_) as typ) = match t with
  | Typ_tup ts -> List.exists typ_needs_printed ts
  | Typ_app (Id_aux (Id "itself",_),_) -> true
  | Typ_app (_, targs) -> is_bitvector_typ typ || List.exists typ_needs_printed_arg targs
  | Typ_fn (t1,t2,_) -> typ_needs_printed t1 || typ_needs_printed t2
  | _ -> false
and typ_needs_printed_arg (Typ_arg_aux (targ, _)) = match targ with
  | Typ_arg_typ t -> typ_needs_printed t
  | _ -> false

let contains_early_return exp =
  fst (fold_exp
  { (Rewriter.compute_exp_alg false (||))
    with e_return = (fun (_, r) -> (true, E_return r)) } exp)

let typ_id_of (Typ_aux (typ, l)) = match typ with
  | Typ_id id -> id
  | Typ_app (register, [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id id, _)), _)])
    when string_of_id register = "register" -> id
  | Typ_app (id, _) -> id
  | _ -> raise (Reporting_basic.err_unreachable l "failed to get type id")

let prefix_recordtype = true
let report = Reporting_basic.err_unreachable
let doc_exp_lem, doc_let_lem =
  let rec top_exp sequential mwords (early_ret : bool) (aexp_needed : bool)
    (E_aux (e, (l,annot)) as full_exp) =
    let expY = top_exp sequential mwords early_ret true in
    let expN = top_exp sequential mwords early_ret false in
    let expV = top_exp sequential mwords early_ret in
    let liftR doc =
      if early_ret && effectful (effect_of full_exp)
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
                   (align (doc_lexp_deref_lem sequential mwords early_ret le ^/^
                      field_ref ^/^ expY e2 ^/^ expY e3 ^/^ expY e)))
            | _ ->
               let deref = doc_lexp_deref_lem sequential mwords early_ret le in
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
                   (align (doc_lexp_deref_lem sequential mwords early_ret le ^/^
                     field_ref ^/^ expY e2 ^/^ expY e)))
            | LEXP_aux (_, lannot) ->
               (match le with
                 | LEXP_aux (_, (_, Some (_, Typ_aux (Typ_app (vector, [_; _; _; Typ_arg_aux (Typ_arg_typ etyp, _)]), _), _)))
                   when is_reftyp etyp && string_of_id vector = "vector" ->
                   (* Special case vectors of register references *)
                   let deref =
                     parens (separate space [
                       string "access";
                       expY (lexp_to_exp le);
                       expY e2
                       ]) in
                   liftR ((prefix 2 1) (string "write_reg") (deref ^/^ expY e))
                 | _ ->
                   let deref = doc_lexp_deref_lem sequential mwords early_ret le in
                   let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot lannot)) then "write_reg_bit" else "write_reg_pos" in
                   liftR ((prefix 2 1) (string call)
                   (deref ^/^ expY e2 ^/^ expY e)))
           )
        (* | LEXP_field (le,id) when is_bit_typ t ->
           liftR ((prefix 2 1)
             (string "write_reg_bitfield")
             (doc_lexp_deref_lem sequential mwords early_ret le ^^ space ^^ string_lit(doc_id_lem id) ^/^ expY e)) *)
        | LEXP_field ((LEXP_aux (_, lannot) as le),id) ->
          let field_ref =
            doc_id_lem (typ_id_of (typ_of_annot lannot)) ^^
            underscore ^^
            doc_id_lem id (*^^
            dot ^^
            string "set_field"*) in
           liftR ((prefix 2 1)
             (string "write_reg_field")
             (doc_lexp_deref_lem sequential mwords early_ret le ^^ space ^^
                field_ref ^/^ expY e))
        (* | (LEXP_id id | LEXP_cast (_,id)), t, Alias alias_info ->
           (match alias_info with
            | Alias_field(reg,field) ->
               let f = match t with
                 | (Tid "bit" | Tabbrev (_,{t=Tid "bit"})) ->
                    string "write_reg_bitfield"
                 | _ -> string "write_reg_field" in
               (prefix 2 1)
                 f
                 (separate space [string reg;string_lit(string field);expY e])
            | Alias_pair(reg1,reg2) ->
               string "write_two_regs" ^^ space ^^ string reg1 ^^ space ^^
                 string reg2 ^^ space ^^ expY e) *)
        | _ ->
           liftR ((prefix 2 1) (string "write_reg") (doc_lexp_deref_lem sequential mwords early_ret le ^/^ expY e)))
    | E_vector_append(le,re) ->
      raise (Reporting_basic.err_unreachable l
        "E_vector_append should have been rewritten before pretty-printing")
       (* let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
       let (call,ta,aexp_needed) =
         if is_bitvector_typ t then
           if not (contains_t_pp_var t)
           then ("bitvector_concat", doc_tannot_lem sequential mwords false t, true)
           else ("bitvector_concat", empty, aexp_needed)
         else ("vector_concat",empty,aexp_needed) in
       let epp =
         align (group (separate space [string call;expY le;expY re])) ^^ ta in
       if aexp_needed then parens epp else epp *)
    | E_cons(le,re) -> doc_op (group (colon^^colon)) (expY le) (expY re)
    | E_if(c,t,e) ->
       let (E_aux (_,(_,cannot))) = c in
       let epp =
         separate space [string "if";group (expY c)] ^^
           break 1 ^^
             (prefix 2 1 (string "then") (expN t)) ^^ (break 1) ^^
               (prefix 2 1 (string "else") (expN e)) in
       if aexp_needed then parens (align epp) else epp
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
       raise (report l "E_for should have been removed till now")
    | E_let(leb,e) ->
       let epp = let_exp sequential mwords early_ret leb ^^ space ^^ string "in" ^^ hardline ^^ expN e in
       if aexp_needed then parens epp else epp
    | E_app(f,args) ->
       begin match f with
       (* temporary hack to make the loop body a function of the temporary variables *)
       | Id_aux ((Id (("foreach_inc" | "foreach_dec" |
                       "foreachM_inc" | "foreachM_dec" ) as loopf),_)) ->
          let [id;indices;body;e5] = args in
          let varspp = match e5 with
            | E_aux (E_tuple vars,_) ->
               let vars = List.map (fun (E_aux (E_id id,_)) -> doc_id_lem id) vars in
               begin match vars with
               | [v] -> v
               | _ -> parens (separate comma vars) end
            | E_aux (E_id id,_) ->
               doc_id_lem id
            | E_aux (E_lit (L_aux (L_unit,_)),_) ->
               string "_" in
          parens (
              (prefix 2 1)
                ((separate space) [string loopf;group (expY indices);expY e5])
                (parens
                   (prefix 1 1 (separate space [string "fun";expY id;varspp;arrow]) (expN body))
                )
            )
       | Id_aux ((Id (("while_PP" | "while_PM" |
                       "while_MP" | "while_MM" |
                       "until_PP" | "until_PM" |
                       "until_MP" | "until_MM") as loopf),_)) ->
          let [cond;body;e5] = args in
          let varspp = match e5 with
            | E_aux (E_tuple vars,_) ->
               let vars = List.map (fun (E_aux (E_id id,_)) -> doc_id_lem id) vars in
               begin match vars with
               | [v] -> v
               | _ -> parens (separate comma vars) end
            | E_aux (E_id id,_) ->
               doc_id_lem id
            | E_aux (E_lit (L_aux (L_unit,_)),_) ->
               string "_" in
          parens (
              (prefix 2 1)
                ((separate space) [string loopf; expY e5])
                ((prefix 0 1)
                  (parens (prefix 1 1 (separate space [string "fun";varspp;arrow]) (expN cond)))
                  (parens (prefix 1 1 (separate space [string "fun";varspp;arrow]) (expN body))))
            )
       (* | Id_aux (Id "append",_) ->
          let [e1;e2] = args in
          let epp = align (expY e1 ^^ space ^^ string "++" ^//^ expY e2) in
          if aexp_needed then parens (align epp) else epp
       | Id_aux (Id "slice_raw",_) ->
          let [e1;e2;e3] = args in
          let t1 = typ_of e1 in
          let eff1 = effect_of e1 in
          let call = if is_bitvector_typ t1 then "bvslice_raw" else "slice_raw" in
          let epp = separate space [string call;expY e1;expY e2;expY e3] in
          let (taepp,aexp_needed) =
            let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
            let eff = effect_of full_exp in
            if typ_needs_printed t && not (contains_t_pp_var t)
            then (align epp ^^ (doc_tannot_lem sequential mwords (effectful eff) t), true)
            else (epp, aexp_needed) in
          if aexp_needed then parens (align taepp) else taepp*)
       | Id_aux (Id "length",_) ->
          (* Another temporary hack: The sizeof rewriting introduces calls to
             "length", and the disambiguation between the length function on
             bitvectors and vectors of other element types should be done by
             the type checker, but type checking after rewriting steps is
             currently broken. *)
          let [arg] = args in
          let targ = typ_of arg in
          let call = if (*mwords &&*) is_bitvector_typ targ then "bitvector_length" else "vector_length" in
          let epp = separate space [string call;expY arg] in
          if aexp_needed then parens (align epp) else epp
       (*)| Id_aux (Id "bool_not", _) ->
          let [a] = args in
          let epp = align (string "~" ^^ expY a) in
          if aexp_needed then parens (align epp) else epp *)
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
             let call = match annot with
               | Some (env, _, _) when Env.is_extern f env ->
                 string (Env.get_extern f env)
               | _ -> doc_id_lem f in
             let argspp = match args with
               | [arg] -> expV true arg
               | args -> parens (align (separate_map (comma ^^ break 0) (expV false) args)) in
             let epp = align (call ^//^ argspp) in
             let (taepp,aexp_needed) =
               let t = (*Env.base_typ_of (env_of full_exp)*) (typ_of full_exp) in
               let eff = effect_of full_exp in
               if typ_needs_printed (Env.base_typ_of (env_of full_exp) t)
               then (align epp ^^ (doc_tannot_lem sequential mwords (effectful eff) t), true)
               else (epp, aexp_needed) in
             liftR (if aexp_needed then parens (align taepp) else taepp)
          end
       end
    | E_vector_access (v,e) ->
      let vtyp = Env.base_typ_of (env_of v) (typ_of v) in
      let (start, len, ord, etyp) = vector_typ_args_of vtyp in
      let ord_suffix = if is_order_inc ord then "_inc" else "_dec" in
      let bit_prefix = if is_bitvector_typ vtyp then "bit" else "" in
      let call = bit_prefix ^ "vector_access" ^ ord_suffix in
      let start_idx = match nexp_simp (start) with
        | Nexp_aux (Nexp_constant i, _) -> expN (simple_num l i)
        | _ ->
          let nc = nc_eq start (nminus len (nconstant 1)) in
          if prove (env_of full_exp) nc
          then string (bit_prefix ^ "vector_length") ^^ space ^^ expY v
          else raise (Reporting_basic.err_unreachable l
            ("cannot pretty print expression " ^ (string_of_exp full_exp) ^
            " with non-constant start index")) in
      let epp = string call ^^ space ^^ parens (separate comma_sp [start_idx;expY v;expY e]) in
      if aexp_needed then parens (align epp) else epp
      (* raise (Reporting_basic.err_unreachable l
        "E_vector_access should have been rewritten before pretty-printing") *)
       (* let eff = effect_of full_exp in
       let epp =
         if has_effect eff BE_rreg then
           separate space [string "read_reg_bit";expY v;expY e]
         else
           let tv = typ_of v in
           let call = if is_bitvector_typ tv then "bvaccess" else "access" in
           separate space [string call;expY v;expY e] in
       if aexp_needed then parens (align epp) else epp*)
    | E_vector_subrange (v,e1,e2) ->
      let vtyp = Env.base_typ_of (env_of v) (typ_of v) in
      let (start, len, ord, etyp) = vector_typ_args_of vtyp in
      let ord_suffix = if is_order_inc ord then "_inc" else "_dec" in
      let bit_prefix = if is_bitvector_typ vtyp then "bit" else "" in
      let call = bit_prefix ^ "vector_subrange" ^ ord_suffix in
      let start_idx = match nexp_simp (start) with
        | Nexp_aux (Nexp_constant i, _) -> expN (simple_num l i)
        | _ ->
          let nc = nc_eq start (nminus len (nconstant 1)) in
          if prove (env_of full_exp) nc
          then string (bit_prefix ^ "vector_length") ^^ space ^^ expY v
          else raise (Reporting_basic.err_unreachable l
            ("cannot pretty print expression " ^ (string_of_exp full_exp) ^
            " with non-constant start index")) in
      let epp = string call ^^ space ^^ parens (separate comma_sp [start_idx;expY v;expY e1;expY e2]) in
      if aexp_needed then parens (align epp) else epp
      (* raise (Reporting_basic.err_unreachable l
        "E_vector_subrange should have been rewritten before pretty-printing") *)
       (* let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
       let eff = effect_of full_exp in
       let (epp,aexp_needed) =
         if has_effect eff BE_rreg then
           let epp = align (string "read_reg_range" ^^ space ^^ expY v ^//^ expY e1 ^//^ expY e2) in
           if typ_needs_printed t && not (contains_t_pp_var t)
           then (epp ^^ doc_tannot_lem sequential mwords true t, true)
           else (epp, aexp_needed)
         else
           if is_bitvector_typ t then
             let bepp = string "bvslice" ^^ space ^^ expY v ^//^ expY e1 ^//^ expY e2 in
             if not (contains_t_pp_var t)
             then (bepp ^^ doc_tannot_lem sequential mwords false t, true)
             else (bepp, aexp_needed)
           else (string "slice" ^^ space ^^ expY v ^//^ expY e1 ^//^ expY e2, aexp_needed) in
       if aexp_needed then parens (align epp) else epp *)
    | E_field((E_aux(_,(l,fannot)) as fexp),id) ->
       let ft = typ_of_annot (l,fannot) in
       (match fannot with
        | Some(env, (Typ_aux (Typ_id tid, _)), _)
        | Some(env, (Typ_aux (Typ_app (Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ (Typ_aux (Typ_id tid, _)), _)]), _)), _)
          when Env.is_regtyp tid env ->
           let t = (* Env.base_typ_of (env_of full_exp) *) (typ_of full_exp) in
           let eff = effect_of full_exp in
           let field_f = doc_id_lem tid ^^ underscore ^^ doc_id_lem id ^^ dot ^^ string "get_field" in
           let (ta,aexp_needed) =
             if typ_needs_printed t
             then (doc_tannot_lem sequential mwords (effectful eff) t, true)
             else (empty, aexp_needed) in
           let epp = field_f ^^ space ^^ (expY fexp) in
           if aexp_needed then parens (align epp ^^ ta) else (epp ^^ ta)
        | Some(env, (Typ_aux (Typ_id tid, _)), _) when Env.is_record tid env ->
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
    | E_id id ->
       let env = env_of full_exp in
       let typ = typ_of full_exp in
       let eff = effect_of full_exp in
       let base_typ = Env.base_typ_of env typ in
       if has_effect eff BE_rreg then
         let epp = separate space [string "read_reg";doc_id_lem id] in
         if is_bitvector_typ base_typ
         then liftR (parens (epp ^^ doc_tannot_lem sequential mwords true base_typ))
         else liftR epp
       else if is_ctor env id then doc_id_lem_ctor id
       else doc_id_lem id
        (*| Base((_,t),Alias alias_info,_,eff,_,_) ->
           (match alias_info with
            | Alias_field(reg,field) ->
                let call = match t.t with
                  | Tid "bit" | Tabbrev (_,{t=Tid "bit"}) -> "read_reg_bitfield"
                  | _ -> "read_reg_field" in
                let ta =
                  if typ_needs_printed t && not (contains_t_pp_var t)
                  then doc_tannot_lem sequential mwords true t else empty in
                let epp = separate space [string call;string reg;string_lit(string field)] ^^ ta in
                if aexp_needed then parens (align epp) else epp
            | Alias_pair(reg1,reg2) ->
                let (call,ta) =
                  if has_effect eff BE_rreg then
                    let ta =
                      if typ_needs_printed t && not (contains_t_pp_var t)
                      then doc_tannot_lem sequential mwords true t else empty in
                    ("read_two_regs", ta)
                  else
                    ("RegisterPair", empty) in
                let epp = separate space [string call;string reg1;string reg2] ^^ ta in
                if aexp_needed then parens (align epp) else epp
            | Alias_extract(reg,start,stop) ->
                let epp =
                  if start = stop then
                    separate space [string "read_reg_bit";string reg;doc_int start]
                  else
                    let ta =
                      if typ_needs_printed t && not (contains_t_pp_var t)
                      then doc_tannot_lem sequential mwords true t else empty in
                    separate space [string "read_reg_range";string reg;doc_int start;doc_int stop] ^^ ta in
                if aexp_needed then parens (align epp) else epp
           )*)
    | E_lit lit -> doc_lit_lem sequential mwords false lit annot
    | E_cast(typ,e) ->
       expV aexp_needed e (*
       (match annot with
        | Base((_,t),External _,_,_,_,_) ->
           (* TODO: Does this case still exist with the new type checker? *)
           let epp = string "read_reg" ^^ space ^^ expY e in
           if typ_needs_printed t && not (contains_t_pp_var t)
           then parens (epp ^^ doc_tannot_lem sequential mwords true t) else epp
        | Base((_,t),_,_,_,_,_) ->
           (match typ with
            | Typ_app (Id_aux (Id "vector",_), [Typ_arg_aux (Typ_arg_nexp(Nexp_aux (Nexp_constant i,_)),_);_;_;_]) ->
               let call =
                 if is_bitvector_typ t then "set_bitvector_start"
                 else "set_vector_start" in
               let epp = (concat [string call;space;string (string_of_int i)]) ^//^
                           expY e in
               if aexp_needed then parens epp else epp
               (*
            | Typ_var (Kid_aux (Var "length",_)) ->
               (* TODO: Does this case still exist with the new type checker? *)
               let call =
                 if is_bitvector_typ t then "set_bitvector_start_to_length"
                 else "set_vector_start_to_length" in
               let epp = (string call) ^//^ expY e in
               if aexp_needed then parens epp else epp
               *)
            | _ -> 
               expV aexp_needed e)) (*(parens (doc_op colon (group (expY e)) (doc_typ_lem typ)))) *)
               *)
    | E_tuple exps ->
       (match exps with (*
        | [e] -> expV aexp_needed e *)
        | _ -> parens (separate_map comma expN exps))
    | E_record(FES_aux(FES_Fexps(fexps,_),_)) ->
       let recordtyp = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _) ->
           (* when Env.is_record tid env -> *)
           tid
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       let epp = anglebars (space ^^ (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp sequential mwords early_ret recordtyp) fexps)) ^^ space) in
       if aexp_needed then parens epp else epp
    | E_record_update(e,(FES_aux(FES_Fexps(fexps,_),_))) ->
       (* let (E_aux (_, (_, eannot))) = e in *)
       let recordtyp = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _)
           when Env.is_record tid env ->
           tid
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       anglebars (doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp sequential mwords early_ret recordtyp) fexps))
    | E_vector exps ->
       let t = Env.base_typ_of (env_of full_exp) (typ_of full_exp) in
       let (start, len, order, etyp) =
         if is_vector_typ t then vector_typ_args_of t
         else raise (Reporting_basic.err_unreachable l
           "E_vector of non-vector type") in
       (*match annot with
        | Base((_,t),_,_,_,_,_) ->
           match t.t with
           | Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; TA_typ etyp])
             | Tabbrev(_,{t= Tapp("vector", [TA_nexp start; TA_nexp len; TA_ord order; TA_typ etyp])}) ->*)
              let dir,dir_out = if is_order_inc order then (true,"true") else (false, "false") in
              let start = match nexp_simp start with
                | Nexp_aux (Nexp_constant i, _) -> string_of_int i
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
              let epp =
                group (separate space [string "Vector"; brackets expspp;string start;string dir_out]) in
              let (epp,aexp_needed) =
                if is_bit_typ etyp && mwords then
                  let bepp = string "vec_to_bvec" ^^ space ^^ parens (align epp) in
                  (bepp ^^ doc_tannot_lem sequential mwords false t, true)
                else (epp,aexp_needed) in
              if aexp_needed then parens (align epp) else epp
       (* *)
    | E_vector_update(v,e1,e2) ->
       let t = typ_of v in
       let (start, len, ord, _) = vector_typ_args_of (Env.base_typ_of (env_of full_exp) t) in
       let ord_suffix = if is_order_inc ord then "_inc" else "_dec" in
       let bit_prefix = if is_bitvector_typ t then "bit" else "" in
       let call = bit_prefix ^ "vector_update_pos" ^ ord_suffix in
       let start_idx = match nexp_simp (start) with
         | Nexp_aux (Nexp_constant i, _) -> expN (simple_num l i)
         | _ ->
           let nc = nc_eq start (nminus len (nconstant 1)) in
           if prove (env_of full_exp) nc
           then string (bit_prefix ^ "vector_length") ^^ space ^^ expY v
           else raise (Reporting_basic.err_unreachable l
             ("cannot pretty print expression " ^ (string_of_exp full_exp) ^
             " with non-constant start index")) in
       let epp = string call ^^ space ^^ parens (separate comma_sp [start_idx;expY v;expY e1;expY e2]) in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update_subrange(v,e1,e2,e3) ->
       let t = typ_of v in
       let (start, len, ord, _) = vector_typ_args_of (Env.base_typ_of (env_of full_exp) t) in
       let ord_suffix = if is_order_inc ord then "_inc" else "_dec" in
       let bit_prefix = if is_bitvector_typ t then "bit" else "" in
       let call = bit_prefix ^ "vector_update_subrange" ^ ord_suffix in
       let start_idx = match nexp_simp (start) with
         | Nexp_aux (Nexp_constant i, _) -> expN (simple_num l i)
         | _ ->
           let nc = nc_eq start (nminus len (nconstant 1)) in
           if prove (env_of full_exp) nc
           then string (bit_prefix ^ "vector_length") ^^ space ^^ expY v
           else raise (Reporting_basic.err_unreachable l
             ("cannot pretty print expression " ^ (string_of_exp full_exp) ^
             " with non-constant start index")) in
       let epp =
         align (string call ^//^
           parens (separate comma_sp
             [start_idx; group (expY v); group (expY e1); group (expY e2); group (expY e3)])) in
       if aexp_needed then parens (align epp) else epp
    | E_list exps ->
       brackets (separate_map semi (expN) exps)
    | E_case(e,pexps) ->
       let only_integers e =
         let typ = typ_of e in
         if Ast_util.is_number typ then
           let e_pp = expY e in
           align (string "toNatural" ^//^ e_pp)
         else
           (* TODO: Where does this come from?? *)
           (match typ with
            | Typ_aux (Typ_tup ([t1;t2;t3;t4;t5] as ts), _) when List.for_all Ast_util.is_number ts ->
               let e_pp = expY e in
               align (string "toNaturalFiveTup" ^//^ e_pp)
            | _ -> expY e)
       in

       (* This is a hack, incomplete. It's because lem does not allow
        pattern-matching on integers *)
       let epp =
         group ((separate space [string "match"; only_integers e; string "with"]) ^/^
                  (separate_map (break 1) (doc_case sequential mwords early_ret) pexps) ^/^
                    (string "end")) in
       if aexp_needed then parens (align epp) else align epp
    | E_exit e -> liftR (separate space [string "exit"; expY e;])
    | E_assert (e1,e2) ->
       let epp = liftR (separate space [string "assert_exp"; expY e1; expY e2]) in
       if aexp_needed then parens (align epp) else align epp
    | E_app_infix (e1,id,e2) ->
       (* TODO: Should have been removed by the new type checker; check with Alasdair *)
       raise (Reporting_basic.err_unreachable l
         "E_app_infix should have been rewritten before pretty-printing")
       (*match annot with
        | Base((_,t),External(Some name),_,_,_,_) ->
           let argpp arg =
             let (E_aux (_,(_,Base((_,t),_,_,_,_,_)))) = arg in
             match t.t with
             | Tapp("vector",_) ->
                 let call =
                   if is_bitvector_typ t then "reset_bitvector_start"
                   else "reset_vector_start" in
                 parens (concat [string call;space;expY arg])
             | _ -> expY arg in
           let epp =
             let aux name = align (argpp e1 ^^ space ^^ string name ^//^ argpp e2) in
             let aux2 name = align (string name ^//^ argpp e1 ^/^ argpp e2) in
             align
               (match name with
                | "power" -> aux2 "pow"

                | "bitwise_and_bit" -> aux "&."
                | "bitwise_or_bit" -> aux "|."
                | "bitwise_xor_bit" -> aux "+."
                | "add" -> aux "+"
                | "minus" -> aux "-"
                | "multiply" -> aux "*"

                | "quot" -> aux2 "quot"
                | "quot_signed" -> aux2 "quot"
                | "modulo" -> aux2 "modulo"
                | "add_vec" -> aux2 "add_VVV"
                | "add_vec_signed" -> aux2 "addS_VVV"
                | "add_overflow_vec" -> aux2 "addO_VVV"
                | "add_overflow_vec_signed" -> aux2 "addSO_VVV"
                | "minus_vec" -> aux2 "minus_VVV"
                | "minus_overflow_vec" -> aux2 "minusO_VVV"
                | "minus_overflow_vec_signed" -> aux2 "minusSO_VVV"
                | "multiply_vec" -> aux2 "mult_VVV"
                | "multiply_vec_signed" -> aux2 "multS_VVV"
                | "mult_overflow_vec" -> aux2 "multO_VVV"
                | "mult_overflow_vec_signed" -> aux2 "multSO_VVV"
                | "quot_vec" -> aux2 "quot_VVV"
                | "quot_vec_signed" -> aux2 "quotS_VVV"
                | "quot_overflow_vec" -> aux2 "quotO_VVV"
                | "quot_overflow_vec_signed" -> aux2 "quotSO_VVV"
                | "mod_vec" -> aux2 "mod_VVV"

                | "add_vec_range" -> aux2 "add_VIV"
                | "add_vec_range_signed" -> aux2 "addS_VIV"
                | "minus_vec_range" -> aux2 "minus_VIV"
                | "mult_vec_range" -> aux2 "mult_VIV"
                | "mult_vec_range_signed" -> aux2 "multS_VIV"
                | "mod_vec_range" -> aux2 "minus_VIV"

                | "add_range_vec" -> aux2 "add_IVV"
                | "add_range_vec_signed" -> aux2 "addS_IVV"
                | "minus_range_vec" -> aux2 "minus_IVV"
                | "mult_range_vec" -> aux2 "mult_IVV"
                | "mult_range_vec_signed" -> aux2 "multS_IVV"

                | "add_range_vec_range" -> aux2 "add_IVI"
                | "add_range_vec_range_signed" -> aux2 "addS_IVI"
                | "minus_range_vec_range" -> aux2 "minus_IVI"

                | "add_vec_range_range" -> aux2 "add_VII"
                | "add_vec_range_range_signed" -> aux2 "addS_VII"
                | "minus_vec_range_range" -> aux2 "minus_VII"
                | "add_vec_vec_range" -> aux2 "add_VVI"
                | "add_vec_vec_range_signed" -> aux2 "addS_VVI"

                | "add_vec_bit" -> aux2 "add_VBV"
                | "add_vec_bit_signed" -> aux2 "addS_VBV"
                | "add_overflow_vec_bit_signed" -> aux2 "addSO_VBV"
                | "minus_vec_bit_signed" -> aux2 "minus_VBV"
                | "minus_overflow_vec_bit" -> aux2 "minusO_VBV"
                | "minus_overflow_vec_bit_signed" -> aux2 "minusSO_VBV"

                | _ ->
                   string name ^//^ parens (expN e1 ^^ comma ^/^ expN e2)) in
           let (epp,aexp_needed) =
             if typ_needs_printed t && not (contains_t_pp_var t)
             then (parens epp ^^ doc_tannot_lem sequential mwords false t, true)
             else (epp, aexp_needed) in
           if aexp_needed then parens (align epp) else epp
        | _ ->
           let epp =
             align (doc_id_lem id ^//^ parens (expN e1 ^^ comma ^/^ expN e2)) in
           if aexp_needed then parens (align epp) else epp*)
    | E_internal_let(lexp, eq_exp, in_exp) ->
       raise (report l "E_internal_lets should have been removed till now")
    (*     (separate
        space
        [string "let internal";
         (match lexp with (LEXP_aux ((LEXP_id id | LEXP_cast (_,id)),_)) -> doc_id_lem id);
         coloneq;
         exp eq_exp;
         string "in"]) ^/^
       exp in_exp *)
    | E_internal_plet (pat,e1,e2) ->
       let epp =
         let b = match e1 with E_aux (E_if _,_) -> true | _ -> false in
         match pat with
         | P_aux (P_wild,_) ->
            (separate space [expV b e1; string ">>"]) ^^ hardline ^^ expN e2
         | _ ->
            (separate space [expV b e1; string ">>= fun";
                             doc_pat_lem sequential mwords true pat;arrow]) ^^ hardline ^^ expN e2 in
       if aexp_needed then parens (align epp) else epp
    | E_internal_return (e1) ->
       separate space [string "return"; expY e1;]
    | E_sizeof nexp ->
      (match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit_lem sequential mwords false (L_aux (L_num i, l)) annot
        | _ ->
          raise (Reporting_basic.err_unreachable l
            "pretty-printing non-constant sizeof expressions to Lem not supported"))
    | E_return r ->
      let ret_monad = if sequential then " : MR regstate" else " : MR" in
      let ta =
        if contains_t_pp_var (typ_of full_exp) || contains_t_pp_var (typ_of r)
        then empty
        else separate space
          [string ret_monad;
          parens (doc_typ_lem sequential mwords (typ_of full_exp));
          parens (doc_typ_lem sequential mwords (typ_of r))] in
      align (parens (string "early_return" ^//^ expV true r ^//^ ta))
    | E_constraint _ | E_comment _ | E_comment_struc _ -> empty
    | E_internal_cast _ | E_internal_exp _ | E_sizeof_internal _ | E_internal_exp_user _ ->
      raise (Reporting_basic.err_unreachable l
        "unsupported internal expression encountered while pretty-printing")
  and let_exp sequential mwords early_ret (LB_aux(lb,_)) = match lb with
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; doc_pat_lem sequential mwords true pat; equals])
              (top_exp sequential mwords early_ret false e)

  and doc_fexp sequential mwords early_ret recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id_lem id
      else doc_id_lem id in
    group (doc_op equals fname (top_exp sequential mwords early_ret true e))

  and doc_case sequential mwords early_ret = function
  | Pat_aux(Pat_exp(pat,e),_) ->
    group (prefix 3 1 (separate space [pipe; doc_pat_lem sequential mwords false pat;arrow])
                  (group (top_exp sequential mwords early_ret false e)))
  | Pat_aux(Pat_when(_,_,_),(l,_)) ->
    raise (Reporting_basic.err_unreachable l
      "guarded pattern expression should have been rewritten before pretty-printing")

  and doc_lexp_deref_lem sequential mwords early_ret ((LEXP_aux(lexp,(l,annot))) as le) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref_lem sequential mwords early_ret le;dot;doc_id_lem id])
    | LEXP_vector(le,e) ->
       parens ((separate space) [string "access";doc_lexp_deref_lem sequential mwords early_ret le;
                                 top_exp sequential mwords early_ret true e])
    | LEXP_id id -> doc_id_lem id
    | LEXP_cast (typ,id) -> doc_id_lem id
    | LEXP_tup lexps -> parens (separate_map comma_sp (doc_lexp_deref_lem sequential mwords early_ret) lexps)
    | _ ->
       raise (Reporting_basic.err_unreachable l ("doc_lexp_deref_lem: Shouldn't happen"))
             (* expose doc_exp_lem and doc_let *)
  in top_exp, let_exp

(*TODO Upcase and downcase type and constructors as needed*)
let doc_type_union_lem sequential mwords (Tu_aux(typ_u,_)) = match typ_u with
  | Tu_ty_id(typ,id) -> separate space [pipe; doc_id_lem_ctor id; string "of";
                                        parens (doc_typ_lem sequential mwords typ)]
  | Tu_id id -> separate space [pipe; doc_id_lem_ctor id]

let rec doc_range_lem (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef_lem sequential mwords (TD_aux(td, (l, annot))) = match td with
  | TD_abbrev(id,nm,(TypSchm_aux (TypSchm_ts (typq, _), _) as typschm)) ->
     doc_op equals
       (separate space [string "type"; doc_id_lem_type id; doc_typquant_items_lem None typq])
       (doc_typschm_lem sequential mwords false typschm)
  | TD_record(id,nm,typq,fs,_) ->
    let fname fid = if prefix_recordtype
                    then concat [doc_id_lem id;string "_";doc_id_lem_type fid;]
                    else doc_id_lem_type fid in
    let f_pp (typ,fid) =
      concat [fname fid;space;colon;space;doc_typ_lem sequential mwords typ; semi] in
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
    let doc_field (ftyp, fid) =
      let reftyp =
        mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
          [mk_typ_arg (Typ_arg_typ rectyp);
           mk_typ_arg (Typ_arg_typ ftyp)])) in
      let rfannot = doc_tannot_lem sequential mwords false reftyp in
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
        | _ -> (0, true) in
      doc_op equals
        (concat [string "let "; parens (concat [doc_id_lem id; underscore; doc_id_lem fid; rfannot])])
        (anglebars (concat [space;
          doc_op equals (string "field_name") (string_lit (doc_id_lem fid)); semi_sp;
          doc_op equals (string "field_start") (string (string_of_int start)); semi_sp;
          doc_op equals (string "field_is_inc") (string (if is_inc then "true" else "false")); semi_sp;
          doc_op equals (string "get_field") (parens (doc_op arrow (string "fun rec_val") get)); semi_sp;
          doc_op equals (string "set_field") (parens (doc_op arrow (string "fun rec_val v") set)); space])) in
    doc_op equals
           (separate space [string "type"; doc_id_lem_type id; doc_typquant_items_lem None typq])
           ((*doc_typquant_lem typq*) (anglebars (space ^^ align fs_doc ^^ space))) ^^ hardline ^^
    if sequential && string_of_id id = "regstate" then empty
    else separate_map hardline doc_field fs
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
         let ar_doc = group (separate_map (break 1) (doc_type_union_lem sequential mwords) ar) in
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
  | TD_register(id,n1,n2,rs) ->
    match n1, n2 with
    | Nexp_aux(Nexp_constant i1,_),Nexp_aux(Nexp_constant i2,_) ->
       let dir_b = i1 < i2 in
       let dir = (if dir_b then "true" else "false") in
       let dir_suffix = (if dir_b then "_inc" else "_dec") in
       let ord = Ord_aux ((if dir_b then Ord_inc else Ord_dec), Parse_ast.Unknown) in
       let size = if dir_b then i2-i1 +1 else i1-i2 + 1 in
       let vtyp = vector_typ (nconstant i1) (nconstant size) ord bit_typ in
       let tannot = doc_tannot_lem sequential mwords false vtyp in
       let doc_rid (r,id) = parens (separate comma_sp [string_lit (doc_id_lem id);
                                                       doc_range_lem r;]) in
       let doc_rids = group (separate_map (semi ^^ (break 1)) doc_rid rs) in
       let doc_field (fr, fid) =
         let i, j = match fr with
         | BF_aux (BF_single i, _) -> (i, i)
         | BF_aux (BF_range (i, j), _) -> (i, j)
         | _ -> raise (Reporting_basic.err_unreachable l "unsupported field type") in
         let fsize = if dir_b then j-i+1 else i-j+1 in
         let ftyp = vector_typ (nconstant i) (nconstant fsize) ord bit_typ in
         let reftyp =
           mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
             [mk_typ_arg (Typ_arg_typ (mk_id_typ id));
              mk_typ_arg (Typ_arg_typ ftyp)])) in
         let rfannot = doc_tannot_lem sequential mwords false reftyp in
         let id_exp id = E_aux (E_id (mk_id id), simple_annot l vtyp) in
         let get, set =
           E_aux (E_vector_subrange (id_exp "reg", simple_num l i, simple_num l j), simple_annot l ftyp),
           E_aux (E_vector_update_subrange (id_exp "reg", simple_num l i, simple_num l j, id_exp "v"), simple_annot l ftyp) in
           (* "bitvector_subrange" ^ dir_suffix ^ " (" ^ string_of_int i1 ^ ", reg, " ^ string_of_int i ^ ", " ^ string_of_int j ^ ")",
           "bitvector_update_subrange" ^ dir_suffix ^ " (" ^ string_of_int i1 ^ ", reg, " ^ string_of_int i ^ ", " ^ string_of_int j ^ ", v)" in *)
         doc_op equals
           (concat [string "let "; parens (concat [doc_id_lem id; underscore; doc_id_lem fid; rfannot])])
           (concat [
             space; langlebar; string " field_name = \"" ^^ doc_id_lem fid ^^ string "\";"; hardline;
             space; space; space; string (" field_start = " ^ string_of_int i ^ ";"); hardline;
             space; space; space; string (" field_is_inc = " ^ dir ^ ";"); hardline;
             space; space; space; string " get_field = (fun reg -> " ^^ doc_exp_lem sequential mwords false false get ^^ string ");"; hardline;
             space; space; space; string " set_field = (fun reg v -> " ^^ doc_exp_lem sequential mwords false false set ^^ string ") "; ranglebar])
       in
       doc_op equals
         (concat [string "type";space;doc_id_lem id])
         (doc_typ_lem sequential mwords vtyp)
       ^^ hardline ^^
       doc_op equals
         (concat [string "let";space;string "cast_";doc_id_lem id;space;string "reg"])
         (string "reg")
       ^^ hardline ^^
       doc_op equals
         (concat [string "let";space;string "cast_to_";doc_id_lem id;space;string "reg"])
         (string "reg")
       ^^ hardline ^^
       (* if sequential then *)
               (* string " = <|" (*; parens (string "reg" ^^ tannot) *)]) ^^ hardline ^^
           string ("  get_field = (fun reg -> " ^ get ^ ");") ^^ hardline ^^
           string ("  set_field = (fun reg v -> " ^ set ^") |>") *)
           (* doc_op equals
             (concat [string "let set_"; doc_id_lem id; underscore; doc_id_lem fid;
               space; parens (separate comma_sp [parens (string "reg" ^^ tannot); string "v"])]) (string set) *)
         (* in *)
         (* doc_op equals
           (concat [string "let";space;string "build_";doc_id_lem id;space;string "regname"])
           (string "Register" ^^ space ^^
              align (separate space [string "regname"; doc_int size; doc_int i1; dir;
                                     break 0 ^^ brackets (align doc_rids)]))
         ^^ hardline ^^ *)
           separate_map hardline doc_field rs
       ^^ hardline ^^
       (* else *)
         (*let doc_rfield (_,id) =
           (doc_op equals)
             (string "let" ^^ space ^^ doc_id_lem id)
             (string "Register_field" ^^ space ^^ string_lit(doc_id_lem id)) in*)
         doc_op equals
           (concat [string "let";space;string "build_";doc_id_lem id;space;string "regname"])
           (string "Register" ^^ space ^^
              align (separate space [string "regname"; doc_int size; doc_int i1; string dir;
                                     break 0 ^^ brackets (align doc_rids)]))
         (*^^ hardline ^^
           separate_map hardline doc_field rs*)
    | _ -> raise (Reporting_basic.err_unreachable l "register with non-constant indices")


let doc_rec_lem (Rec_aux(r,_)) = match r with
  | Rec_nonrec -> space
  | Rec_rec -> space ^^ string "rec" ^^ space

let doc_tannot_opt_lem sequential mwords (Typ_annot_opt_aux(t,_)) = match t with
  | Typ_annot_opt_some(tq,typ) -> (*doc_typquant_lem tq*) (doc_typ_lem sequential mwords typ)

let doc_fun_body_lem sequential mwords exp =
  let early_ret = contains_early_return exp in
  let doc_exp = doc_exp_lem sequential mwords early_ret false exp in
  if early_ret
  then align (string "catch_early_return" ^//^ parens (doc_exp))
  else doc_exp

let doc_funcl_lem sequential mwords (FCL_aux(FCL_Funcl(id,pat,exp),_)) =
  group (prefix 3 1 ((doc_pat_lem sequential mwords false pat) ^^ space ^^ arrow)
    (doc_fun_body_lem sequential mwords exp))

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_,_),_))::_ -> id

module StringSet = Set.Make(String)

let doc_fundef_rhs_lem sequential mwords (FD_aux(FD_function(r, typa, efa, funcls),fannot) as fd) =
  match funcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux(FCL_Funcl(id,pat,exp),_)] ->
    (prefix 2 1)
      ((separate space)
         [doc_id_lem id;
          (doc_pat_lem sequential mwords true pat);
          equals])
      (doc_fun_body_lem sequential mwords exp)
  | _ ->
    let clauses =
      (separate_map (break 1))
        (fun fcl -> separate space [pipe;doc_funcl_lem sequential mwords fcl]) funcls in
    (prefix 2 1)
      ((separate space) [doc_id_lem (id_of_fundef fd);equals;string "function"])
      (clauses ^/^ string "end")

let doc_mutrec_lem sequential mwords = function
  | [] -> failwith "DEF_internal_mutrec with empty function list"
  | fundefs ->
    string "let rec " ^^
    separate_map (hardline ^^ string "and ")
      (doc_fundef_rhs_lem sequential mwords) fundefs

let rec doc_fundef_lem sequential mwords (FD_aux(FD_function(r, typa, efa, fcls),fannot) as fd) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | FCL_aux (FCL_Funcl(id,_,exp),_) :: _
    when string_of_id id = "execute" (*|| string_of_id id = "initial_analysis"*) ->
    let (_,auxiliary_functions,clauses) =
      List.fold_left
        (fun (already_used_fnames,auxiliary_functions,clauses) funcl ->
          match funcl with
          | FCL_aux (FCL_Funcl (Id_aux (Id _,l),pat,exp),annot) ->
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
             let aux_fname = pick_name_not_clashing_with already_used_fnames (string_of_id id ^ "_" ^ ctor) in
             let already_used_fnames = StringSet.add aux_fname already_used_fnames in
             let fcl = FCL_aux (FCL_Funcl (Id_aux (Id aux_fname,l),
                                           P_aux (P_tup argspat,pannot),exp),annot) in
             let auxiliary_functions =
                auxiliary_functions ^^ hardline ^^ hardline ^^
                  doc_fundef_lem sequential mwords (FD_aux (FD_function(r,typa,efa,[fcl]),fannot)) in
             (* Bind complex patterns to names so that we can pass them to the
                auxiliary function *)
             let name_pat idx (P_aux (p,a)) = match p with
               | P_as (pat,_) -> P_aux (p,a) (* already named *)
               | P_lit _ -> P_aux (p,a) (* no need to name a literal *)
               | P_id _ -> P_aux (p,a) (* no need to name an identifier *)
               | _ -> P_aux (P_as (P_aux (p,a), Id_aux (Id ("arg" ^ string_of_int idx),l)),a) in
             let named_argspat = List.mapi name_pat argspat in
             let named_pat = P_aux (P_app (Id_aux (Id ctor,l),named_argspat),pannot) in
             let doc_arg idx (P_aux (p,(l,a))) = match p with
               | P_as (pat,id) -> doc_id_lem id
               | P_lit lit -> doc_lit_lem sequential mwords false lit a
               | P_id id -> doc_id_lem id
               | _ -> string ("arg" ^ string_of_int idx) in
             let clauses =
               clauses ^^ (break 1) ^^
                 (separate space
                    [pipe;doc_pat_lem sequential mwords false named_pat;arrow;
                     string aux_fname;
                     parens (separate comma (List.mapi doc_arg named_argspat))]) in
             (already_used_fnames,auxiliary_functions,clauses)
        ) (StringSet.empty,empty,empty) fcls in

    auxiliary_functions ^^ hardline ^^ hardline ^^
    (prefix 2 1)
      ((separate space) [string "let" ^^ doc_rec_lem r ^^ doc_id_lem id;equals;string "function"])
      (clauses ^/^ string "end")
  | FCL_aux (FCL_Funcl(id,_,exp),_) :: _
    when not (Env.is_extern id (env_of exp)) ->
    string "let" ^^ (doc_rec_lem r) ^^ (doc_fundef_rhs_lem sequential mwords fd)
  | _ -> empty



let doc_dec_lem sequential (DEC_aux (reg, ((l, _) as annot))) =
  match reg with
  | DEC_reg(typ,id) ->
     if sequential then empty
     else
       let env = env_of_annot annot in
       (match typ with
        | Typ_aux (Typ_id idt, _) when Env.is_regtyp idt env ->
          separate space [string "let";doc_id_lem id;equals;
                          string "build_" ^^ string (string_of_id idt);string_lit (doc_id_lem id)] ^/^ hardline
        | _ ->
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
            else raise (Reporting_basic.err_unreachable l
              ("can't deal with register type " ^ string_of_typ typ))
          else raise (Reporting_basic.err_unreachable l
            ("can't deal with register type " ^ string_of_typ typ)))
  | DEC_alias(id,alspec) -> empty
  | DEC_typ_alias(typ,id,alspec) -> empty

let doc_spec_lem sequential mwords (VS_aux (valspec,annot)) =
  match valspec with
  | VS_val_spec (typschm,id,None,_) ->
     (* let (TypSchm_aux (TypSchm_ts (tq, typ), _)) = typschm in
     if contains_t_pp_var typ then empty else *)
     separate space [string "val"; doc_id_lem id; string ":";doc_typschm_lem sequential mwords true typschm] ^/^ hardline 
  | VS_val_spec (_,_,Some _,_) -> empty

let rec doc_def_lem sequential mwords def =
  (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
  match def with
  | DEF_spec v_spec -> (empty,doc_spec_lem sequential mwords v_spec)
  | DEF_fixity _ -> (empty,empty)
  | DEF_overload _ -> (empty,empty)
  | DEF_type t_def -> (group (doc_typdef_lem sequential mwords t_def) ^/^ hardline,empty)
  | DEF_reg_dec dec -> (group (doc_dec_lem sequential dec),empty)

  | DEF_default df -> (empty,empty)
  | DEF_fundef f_def -> (empty,group (doc_fundef_lem sequential mwords f_def) ^/^ hardline)
  | DEF_internal_mutrec fundefs ->
     (empty, doc_mutrec_lem sequential mwords fundefs ^/^ hardline)
  | DEF_val lbind -> (empty,group (doc_let_lem sequential mwords false lbind) ^/^ hardline)
  | DEF_scattered sdef -> failwith "doc_def_lem: shoulnd't have DEF_scattered at this point"

  | DEF_kind _ -> (empty,empty)

  | DEF_comm (DC_comm s) -> (empty,comment (string s))
  | DEF_comm (DC_comm_struct d) ->
     let (typdefs,vdefs) = doc_def_lem sequential mwords d in
     (empty,comment (typdefs ^^ hardline ^^ vdefs))


let doc_defs_lem sequential mwords (Defs defs) =
  let (typdefs,valdefs) = List.split (List.map (doc_def_lem sequential mwords) defs) in
  (separate empty typdefs,separate empty valdefs)

let find_regtypes (Defs defs) =
  List.fold_left
    (fun acc def ->
      match def with
      | DEF_type (TD_aux(TD_register (Id_aux (Id tname, _),_,_,_),_)) -> tname :: acc
      | _ -> acc
    ) [] defs

let find_registers (Defs defs) =
  List.fold_left
    (fun acc def ->
      match def with
      | DEF_reg_dec (DEC_aux(DEC_reg (typ, id), annot)) ->
        let env = match annot with
          | (_, Some (env, _, _)) -> env
          | _ -> Env.empty in
        (typ, id, env) :: acc
      | _ -> acc
    ) [] defs

let doc_regstate_lem mwords registers =
  let l = Parse_ast.Unknown in
  let annot = (l, None) in
  let regstate = match registers with
    | [] ->
      TD_abbrev (
        Id_aux (Id "regstate", l),
        Name_sect_aux (Name_sect_none, l),
        TypSchm_aux (TypSchm_ts (TypQ_aux (TypQ_tq [], l), unit_typ), l))
    | _ ->
      TD_record (
        Id_aux (Id "regstate", l),
        Name_sect_aux (Name_sect_none, l),
        TypQ_aux (TypQ_tq [], l),
        List.map (fun (typ, id, env) -> (typ, id)) registers,
        false)
  in
  let initregstate =
    if !Initial_check.opt_undefined_gen then
      let exp = match registers with
        | [] -> E_aux (E_lit (mk_lit L_unit), (l, Some (Env.empty, unit_typ, no_effect)))
        | _ ->
           let initreg (typ, id, env) =
             let annot typ = Some (env, typ, no_effect) in
             let initval = undefined_of_typ mwords l annot typ in
             FE_aux (FE_Fexp (id, initval), (l, annot typ)) in
           E_aux (
             E_record (FES_aux (FES_Fexps (List.map initreg registers, false), annot)),
             (l, Some (Env.empty, mk_id_typ (mk_id "regstate"), no_effect)))
      in
      doc_op equals (string "let initial_regstate") (doc_exp_lem true mwords false false exp)
    else empty
  in
  concat [
    doc_typdef_lem true mwords (TD_aux (regstate, annot)); hardline;
    hardline;
    string "type _M 'a = M regstate 'a"
  ],
  initregstate

let doc_register_refs_lem registers =
  let doc_register_ref (typ, id, env) =
    let idd = doc_id_lem id in
    let field = if prefix_recordtype then string "regstate_" ^^ idd else idd in
    let base_typ = Env.base_typ_of env typ in
    let (start, is_inc) =
      try
        let (start, _, ord, _) = vector_typ_args_of base_typ in
        match nexp_simp start with
        | Nexp_aux (Nexp_constant i, _) -> (i, is_order_inc ord)
        | _ ->
          raise (Reporting_basic.err_unreachable Parse_ast.Unknown
            ("register " ^ string_of_id id ^ " has non-constant start index " ^ string_of_nexp start))
      with
      | _ -> (0, true) in
    concat [string "let "; idd; string " = <|"; hardline;
      string "  reg_name = \""; idd; string "\";"; hardline;
      string "  reg_start = "; string (string_of_int start); string ";"; hardline;
      string "  reg_is_inc = "; string (if is_inc then "true" else "false"); string ";"; hardline;
      string "  read_from = (fun s -> s."; field; string ");"; hardline;
      string "  write_to = (fun s v -> (<| s with "; field; string " = v |>)) |>"] in
  separate_map hardline doc_register_ref registers

let pp_defs_lem sequential mwords (types_file,types_modules) (defs_file,defs_modules) d top_line =
  (* let regtypes = find_regtypes d in *)
  let (typdefs,valdefs) = doc_defs_lem sequential mwords d in
  let regstate_def, initregstate_def = doc_regstate_lem mwords (find_registers d) in
  let register_refs = doc_register_refs_lem (find_registers d) in
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
        typdefs; hardline;
        hardline;
        if sequential then
          concat [regstate_def; hardline;
          hardline;
          register_refs]
        else
          concat [string "type _M 'a = M 'a"; hardline]
        ]);
  (* (print types_seq_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "open import";string lib]) types_seq_modules;hardline;
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
        typdefs_seq; hardline;
        hardline;
        regstate_def; hardline;
        hardline;
        register_refs]); *)
  (print defs_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "open import";string lib]) defs_modules;hardline;
        hardline;
        valdefs;
        hardline;
        initregstate_def]);
  (* (print state_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "open import";string lib]) state_modules;hardline;
        hardline;
        valdefs_seq]); *)
