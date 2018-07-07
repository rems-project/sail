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

  fix_id
  doc_quant_item on constraints
  type quantifiers in records, unions
  multiple update notation for records
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

let opt_undef_axioms = ref false

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
let enclose_record_update = enclose (string "{[ ") (string " ]}")
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
  | "Z"
  | "mod"
  | "M"
    -> name ^ "'"
  | _ ->
     if String.contains name '#' then
       fix_id remove_tick (String.concat "_" (Util.split_on_char '#' name))
     else if String.contains name '?' then
       fix_id remove_tick (String.concat "_pat_" (Util.split_on_char '?' name))
     else if String.contains name '^' then
       fix_id remove_tick (String.concat "__" (Util.split_on_char '^' name))
     else if name.[0] = '\'' then
       let var = String.sub name 1 (String.length name - 1) in
       if remove_tick then fix_id remove_tick var else (var ^ "'")
     else if is_number_char(name.[0]) then
       ("v" ^ name ^ "'")
     else name

let doc_id (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x -> string (Util.zencode_string ("op " ^ x))

let doc_id_type (Id_aux(i,_)) =
  match i with
  | Id("int") -> string "Z"
  | Id("nat") -> string "Z"
  | Id i -> string (fix_id false i)
  | DeIid x -> string (Util.zencode_string ("op " ^ x))

let doc_id_ctor (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x -> string (Util.zencode_string ("op " ^ x))

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
  (* Print according to Coq's precedence rules *)
  let rec plussub (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_sum (n1, n2) -> separate space [plussub n1; plus; mul n2]
    | Nexp_minus (n1, n2) -> separate space [plussub n1; minus; mul n2]
    | _ -> mul nexp
  and mul (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_times (n1, n2) -> separate space [mul n1; star; uneg n2]
    | _ -> uneg nexp
  and uneg (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_neg n -> separate space [minus; uneg n]
    | _ -> exp nexp
  and exp (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_exp n -> separate space [string "2"; caret; exp n]
    | _ -> app nexp
  and app (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_app (Id_aux (Id "div",_), [n1;n2])
        -> separate space [string "Z.quot"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "mod",_), [n1;n2])
        -> separate space [string "Z.rem"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "abs_atom",_), [n1])
        -> separate space [string "Z.abs"; atomic n1]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_constant i -> string (Big_int.to_string i)
    | Nexp_var v -> doc_var_lem ctx v
    | Nexp_id id -> doc_id id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _
    | Nexp_app (Id_aux (Id ("div"|"mod"),_), [_;_])
    | Nexp_app (Id_aux (Id "abs_atom",_), [_])
        -> parens (plussub nexp)
    | _ ->
       raise (Reporting_basic.err_unreachable l
                ("cannot pretty-print nexp \"" ^ string_of_nexp nexp ^ "\""))
  in atomic (nexp_simp nexp)

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

(* In existential types we don't want term-level versions of the
   type variables to stick around *)
let drop_duplicate_atoms kids ty =
  let kids = KidSet.of_list kids in
  let rec aux_typ (Typ_aux (typ,l) as full_typ) =
    match typ with
    | Typ_id _
    | Typ_var _ -> Some full_typ
    | Typ_fn (arg,res,eff) -> raise (Reporting_basic.err_unreachable l "Function type nested inside existential")
    | Typ_tup typs ->
       (match Util.map_filter aux_typ typs with
       | [] -> None
       | typs' -> Some (Typ_aux (Typ_tup typs',l)))
    | Typ_exist _ -> raise (Reporting_basic.err_unreachable l "Nested existential type")
       (* This is an AST type, don't need to check for equivalent nexps *)
    | Typ_app (Id_aux (Id "atom",_), [Typ_arg_aux (Typ_arg_nexp (Nexp_aux (Nexp_var kid,_)),_)])
        when KidSet.mem kid kids ->
       None
    (* Don't recurse into type arguments, removing stuff there
       would be weird (and difficult) *)
    | Typ_app _ -> Some full_typ
  in aux_typ ty

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

let maybe_expand_range_type (Typ_aux (typ,l) as full_typ) =
  match typ with
  | Typ_app(Id_aux (Id "range", _), [Typ_arg_aux(Typ_arg_nexp low,_);
                                     Typ_arg_aux(Typ_arg_nexp high,_)]) ->
         (* TODO: avoid name clashes *)
     let kid = mk_kid "rangevar" in
     let var = nvar kid in
     let nc = nc_and (nc_lteq low var) (nc_lteq var high) in
     Some (Typ_aux (Typ_exist ([kid], nc, atom_typ var),Parse_ast.Generated l))
  | _ -> None

let expand_range_type typ = Util.option_default typ (maybe_expand_range_type typ)

let doc_arithfact ctxt nc =
  string "ArithFact" ^^ space ^^ parens (doc_nc ctxt nc)

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
           | _ -> string "vec" ^^ space ^^ typ elem_typ ^^ space ^^ doc_nexp ctx (nexp_simp m) in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [Typ_arg_aux (Typ_arg_typ etyp, _)]) ->
         let tpp = string "register_ref regstate register_value " ^^ typ etyp in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _), _) ->
         (match maybe_expand_range_type ty with
         | Some typ -> atomic_typ atyp_needed typ
         | None -> raise (Reporting_basic.err_unreachable l "Bad range type"))
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
      | Typ_exist (kids,nc,ty) -> begin
        let add_tyvar tpp kid =
          braces (separate space [doc_var_lem ctx kid; colon; string "Z"; ampersand; tpp])
        in
        match drop_duplicate_atoms kids ty with
        | Some ty ->
           let tpp = typ ty in
           let tpp = match nc with NC_aux (NC_true,_) -> tpp | _ -> 
             braces (separate space [underscore; colon; parens (doc_arithfact ctx nc); ampersand; tpp])
           in
           List.fold_left add_tyvar tpp kids
        | None ->
           match nc with
(*           | NC_aux (NC_true,_) -> List.fold_left add_tyvar (string "Z") (List.tl kids)*)
           | _ -> List.fold_left add_tyvar (doc_arithfact ctx nc) kids
      end
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
    if eff then
      if ctxt.early_ret
      then string " : MR " ^^ parens ta ^^ string " _"
      else string " : M " ^^ parens ta
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
     utf8string "(Fail \"undefined value of unsupported type\")"
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
  | QI_const nc -> Some (bquote ^^ braces (doc_arithfact ctx nc))

let doc_typquant_items ctx delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     separate_opt space (doc_quant_item_id ctx delimit) qis ^^
     separate_opt space (doc_quant_item_constr ctx delimit) qis
  | TypQ_no_forall -> empty

let doc_typquant_items_separate ctx delimit (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     Util.map_filter (doc_quant_item_id ctx delimit) qis,
     Util.map_filter (doc_quant_item_constr ctx delimit) qis
  | TypQ_no_forall -> [], []

let doc_typquant ctx (TypQ_aux(tq,_)) typ = match tq with
| TypQ_tq ((_ :: _) as qs) ->
   string "forall " ^^ separate_opt space (doc_quant_item_id ctx braces) qs ^/^
     separate_opt space (doc_quant_item_constr ctx parens) qs ^^ string ", " ^^ typ
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

let is_auto_decomposed_exist env typ =
  let typ = expand_range_type typ in
  match destruct_exist env typ with
  | Some (kids, nc, (Typ_aux (Typ_app (id, _),_) as typ')) when string_of_id id = "atom" -> Some typ'
  | _ -> None

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat ctxt apat_needed (P_aux (p,(l,annot)) as pat, typ) =
  let env = env_of_annot (l,annot) in
  let typ = Env.expand_synonyms env typ in
  match is_auto_decomposed_exist env typ with
  | Some typ' ->
     let pat_pp = doc_pat ctxt true (pat, typ') in
     let pat_pp = separate space [string "existT"; underscore; pat_pp; underscore] in
     if apat_needed then parens pat_pp else pat_pp
  | None ->
     match p with
     (* Special case translation of the None constructor to remove the unit arg *)
     | P_app(id, _) when string_of_id id = "None" -> string "None"
     | P_app(id, ((_ :: _) as pats)) -> begin
        (* Following the type checker to get the subpattern types, TODO perhaps ought
           to persuade the type checker to output these somehow. *)
       let (typq, ctor_typ) = Env.get_val_spec id env in
       let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with
         | Typ_tup typs -> typs
         | _ -> [typ]
       in
       let arg_typs =
         match Env.expand_synonyms env ctor_typ with
         | Typ_aux (Typ_fn (arg_typ, ret_typ, _), _) ->
            (* The FIXME comes from the typechecker code, not sure what it's about... *)
            let unifiers, _, _ (* FIXME! *) = unify l env ret_typ typ in
            let arg_typ' = subst_unifiers unifiers arg_typ in
            untuple arg_typ'
         | _ -> assert false
       in
       let ppp = doc_unop (doc_id_ctor id)
         (parens (separate_map comma (doc_pat ctxt true) (List.combine pats arg_typs))) in
       if apat_needed then parens ppp else ppp
     end
     | P_app(id, []) -> doc_id_ctor id
     | P_lit lit  -> doc_lit lit
     | P_wild -> underscore
     | P_id id -> doc_id id
     | P_var(p,_) -> doc_pat ctxt true (p, typ)
     | P_as(p,id) -> parens (separate space [doc_pat ctxt true (p, typ); string "as"; doc_id id])
     | P_typ(ptyp,p) ->
        let doc_p = doc_pat ctxt true (p, typ) in
        doc_p
     (* Type annotations aren't allowed everywhere in patterns in Coq *)
     (*parens (doc_op colon doc_p (doc_typ typ))*)
     | P_vector pats ->
        let el_typ =
          match destruct_vector env typ with
          | Some (_,_,t) -> t
          | None -> raise (Reporting_basic.err_unreachable l "vector pattern doesn't have vector type")
        in
        let ppp = brackets (separate_map semi (fun p -> doc_pat ctxt true (p,el_typ)) pats) in
        if apat_needed then parens ppp else ppp
     | P_vector_concat pats ->
        raise (Reporting_basic.err_unreachable l
                 "vector concatenation patterns should have been removed before pretty-printing")
     | P_tup pats  ->
        let typs = match typ with
          | Typ_aux (Typ_tup typs, _) -> typs
          | _ -> raise (Reporting_basic.err_unreachable l "tuple pattern doesn't have tuple type")
        in
        (match pats, typs with
        | [p], [typ'] -> doc_pat ctxt apat_needed (p, typ')
        | [_], _ -> raise (Reporting_basic.err_unreachable l "tuple pattern length does not match tuple type length")
        | _ -> parens (separate_map comma_sp (doc_pat ctxt false) (List.combine pats typs)))
     | P_list pats ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [Typ_arg_aux (Typ_arg_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting_basic.err_unreachable l "list pattern not a list")
        in
        brackets (separate_map semi (fun p -> doc_pat ctxt false (p, el_typ)) pats)
     | P_cons (p,p') ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [Typ_arg_aux (Typ_arg_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting_basic.err_unreachable l "list pattern not a list")
        in
        doc_op (string "::") (doc_pat ctxt true (p, el_typ)) (doc_pat ctxt true (p', typ))
     | P_record (_,_) -> empty (* TODO *)

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

(* Decide whether two nexps used in a vector size are similar; if not
   a cast will be inserted *)
let similar_nexps n1 n2 =
  let rec same_nexp_shape (Nexp_aux (n1,_)) (Nexp_aux (n2,_)) =
    match n1, n2 with
    | Nexp_id _, Nexp_id _
    | Nexp_var _, Nexp_var _
      -> true
    | Nexp_constant c1, Nexp_constant c2 -> Nat_big_num.equal c1 c2
    | Nexp_app (f1,args1), Nexp_app (f2,args2) ->
       Id.compare f1 f2 == 0 && List.for_all2 same_nexp_shape args1 args2
    | Nexp_times (n1,n2), Nexp_times (n3,n4)
    | Nexp_sum (n1,n2), Nexp_sum (n3,n4)
    | Nexp_minus (n1,n2), Nexp_minus (n3,n4)
      -> same_nexp_shape n1 n3 && same_nexp_shape n2 n4
    | Nexp_exp n1, Nexp_exp n2
    | Nexp_neg n1, Nexp_neg n2
      -> same_nexp_shape n1 n2
    | _ -> false
  in if same_nexp_shape n1 n2 then true else false

let constraint_fns = ["Z.leb"; "Z.geb"; "Z.ltb"; "Z.gtb"; "Z.eqb"]

let condition_produces_constraint exp =
  (* Cheat a little - this isn't quite the right environment for subexpressions
     but will have all of the relevant functions in it. *)
  let env = env_of exp in
  Rewriter.fold_exp
    { (Rewriter.pure_exp_alg false (||)) with
      Rewriter.e_app = fun (f,bs) ->
        List.exists (fun x -> x) bs ||
        (Env.is_extern f env "coq" &&
           let f' = Env.get_extern f env "coq" in
           List.exists (fun id -> String.compare f' id == 0) constraint_fns)
    } exp

let prefix_recordtype = true
let report = Reporting_basic.err_unreachable
let doc_exp_lem, doc_let_lem =
  let rec top_exp (ctxt : context) (aexp_needed : bool)
    (E_aux (e, (l,annot)) as full_exp) =
    let expY = top_exp ctxt true in
    let expN = top_exp ctxt false in
    let expV = top_exp ctxt in
    let wrap_parens doc = if aexp_needed then parens (doc) else doc in
    let maybe_add_exist epp =
      let env = env_of full_exp in
      let typ = Env.expand_synonyms env (typ_of full_exp) in
      let typ = expand_range_type typ in
      match destruct_exist env typ with
      | None -> epp
      | Some _ ->
         let epp = string "build_ex" ^/^ epp in
         if aexp_needed then parens epp else epp
    in
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
       | Id_aux (Id "and_bool", _) | Id_aux (Id "or_bool", _)
         when effectful (effect_of full_exp) ->
          let call = doc_id (append_id f "M") in
          wrap_parens (hang 2 (flow (break 1) (call :: List.map expY args)))
       (* temporary hack to make the loop body a function of the temporary variables *)
       | Id_aux (Id "None", _) as none -> doc_id_ctor none
       | Id_aux (Id "foreach", _) ->
          begin
            match args with
            | [from_exp; to_exp; step_exp; ord_exp; vartuple; body] ->
               let loopvar, body = match body with
                 | E_aux (E_let (LB_aux (LB_val (_, _), _),
                   E_aux (E_let (LB_aux (LB_val (_, _), _),
                   E_aux (E_if (_,
                   E_aux (E_let (LB_aux (LB_val (
                     ((P_aux (P_typ (_, P_aux (P_var (P_aux (P_id id, _), _), _)), _))
                     | (P_aux (P_var (P_aux (P_id id, _), _), _))
                     | (P_aux (P_id id, _))), _), _),
                     body), _), _), _)), _)), _) -> id, body
                 | _ -> raise (Reporting_basic.err_unreachable l ("Unable to find loop variable in " ^ string_of_exp body)) in
               let dir = match ord_exp with
                 | E_aux (E_lit (L_aux (L_false, _)), _) -> "_down"
                 | E_aux (E_lit (L_aux (L_true, _)), _) -> "_up"
                 | _ -> raise (Reporting_basic.err_unreachable l ("Unexpected loop direction " ^ string_of_exp ord_exp))
               in
               let combinator = if effectful (effect_of body) then "foreach_ZM" else "foreach_Z" in
               let combinator = combinator ^ dir in
               let used_vars_body = find_e_ids body in
               let body_lambda =
                 (* Work around indentation issues in Lem when translating
                    tuple or literal unit patterns to Isabelle *)
                 match fst (uncast_exp vartuple) with
                   | E_aux (E_tuple _, _)
                     when not (IdSet.mem (mk_id "varstup") used_vars_body)->
                      separate space [string "fun"; doc_id loopvar; string "_"; string "varstup"; bigarrow]
                      ^^ break 1 ^^
                      separate space [string "let"; expY vartuple; string ":= varstup in"]
                   | E_aux (E_lit (L_aux (L_unit, _)), _)
                     when not (IdSet.mem (mk_id "unit_var") used_vars_body) ->
                      separate space [string "fun"; doc_id loopvar; string "_"; string "unit_var"; bigarrow]
                   | _ ->
                      separate space [string "fun"; doc_id loopvar; string "_"; expY vartuple; bigarrow]
               in
               parens (
                   (prefix 2 1)
                     ((separate space) [string combinator;
                                        expY from_exp; expY to_exp; expY step_exp;
                                        expY vartuple])
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
          let env = env_of_annot (l,annot) in
          if Env.is_union_constructor f env then
            let epp =
              match args with
              | [] -> doc_id_ctor f
              | [arg] -> doc_id_ctor f ^^ space ^^ expV true arg
              | _ ->
                 doc_id_ctor f ^^ space ^^ 
                   parens (separate_map comma (expV false) args) in
            if aexp_needed then parens (align epp) else epp
          else
            let call, is_extern =
              if Env.is_extern f env "coq"
              then string (Env.get_extern f env "coq"), true
              else doc_id f, false in
            let (tqs,fn_ty) = Env.get_val_spec_orig f env in
            let arg_typs, ret_typ, eff = match fn_ty with
              | Typ_aux (Typ_fn (arg_typ,ret_typ,eff),_) ->
                 (match arg_typ with
                 | Typ_aux (Typ_tup typs,_) -> typs, ret_typ, eff
                 | _ -> [arg_typ], ret_typ, eff)
              | _ -> raise (Reporting_basic.err_unreachable l "Function not a function type")
            in
            (* Insert existential unpacking of arguments where necessary *)
            let doc_arg arg typ_from_fn =
              let arg_pp = expY arg in
              let arg_ty = expand_range_type (Env.expand_synonyms (env_of arg) (typ_of arg)) in
              let typ_from_fn = expand_range_type (Env.expand_synonyms (env_of arg) typ_from_fn) in
              (* TODO: more sophisticated check *)
              match destruct_exist env arg_ty, destruct_exist env typ_from_fn with
              | Some _, None -> parens (string "projT1 " ^^ arg_pp)
              (* Usually existentials have already been built elsewhere, but this
                 is useful for (e.g.) ranges *)
              | None, Some _ -> parens (string "build_ex " ^^ arg_pp)
              | _, _ -> arg_pp
            in
            let epp = hang 2 (flow (break 1) (call :: List.map2 doc_arg args arg_typs)) in
            (* Unpack existential result *)
            let inst = instantiation_of full_exp in
            let inst = KBindings.fold (fun k u m -> KBindings.add (orig_kid k) u m) inst KBindings.empty in
            let ret_typ_inst = subst_unifiers inst ret_typ in
            let unpack,build_ex,autocast =
              let ann_typ = Env.expand_synonyms env (typ_of_annot (l,annot)) in
              let ann_typ = expand_range_type ann_typ in
              let ret_typ_inst = expand_range_type (Env.expand_synonyms env ret_typ_inst) in
              let unpack, build_ex, in_typ, out_typ =
                match ret_typ_inst, ann_typ with
                | Typ_aux (Typ_exist (_,_,t1),_), Typ_aux (Typ_exist (_,_,t2),_) ->
                   if alpha_equivalent env ret_typ_inst ann_typ
                   then false,false,t1,t2
                   else true,true,t1,t2
                | Typ_aux (Typ_exist (_,_,t1),_),t2 -> true,false,t1,t2
                | t1, Typ_aux (Typ_exist (_,_,t2),_) -> false,true,t1,t2
                | t1, t2 -> false,false,t1,t2
              in
              let autocast =
                (* Avoid using helper functions which simplify the nexps *)
                is_bitvector_typ in_typ && is_bitvector_typ out_typ &&
                match in_typ, out_typ with
                | Typ_aux (Typ_app (_,[Typ_arg_aux (Typ_arg_nexp n1,_);_;_]),_),
                  Typ_aux (Typ_app (_,[Typ_arg_aux (Typ_arg_nexp n2,_);_;_]),_) ->
                   not (similar_nexps n1 n2)
                | _ -> false
              in unpack,build_ex,autocast
            in
            let autocast_id = if effectful eff then "autocast_m" else "autocast" in
            let epp = if unpack then string "projT1" ^^ space ^^ parens epp else epp in
            let epp = if autocast then string autocast_id ^^ space ^^ parens epp else epp in
            let epp = if build_ex then string "build_ex" ^^ space ^^ parens epp else epp in
            liftR (if aexp_needed then parens (align epp) else epp)
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
           expY fexp ^^ dot ^^ parens fname
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
       else maybe_add_exist (doc_id id)
    | E_lit lit -> maybe_add_exist (doc_lit lit)
    | E_cast(typ,e) ->
       let epp = expV true e in
       let epp = epp ^/^ doc_tannot_lem ctxt (env_of e) (effectful (effect_of e)) typ in
       let env = env_of_annot (l,annot) in
       let unpack,build_ex =
         let ann_typ = Env.expand_synonyms env (typ_of_annot (l,annot)) in
         let ann_typ = expand_range_type ann_typ in
         let cast_typ = expand_range_type (Env.expand_synonyms env typ) in
         match cast_typ, ann_typ with
         | Typ_aux (Typ_exist _,_), Typ_aux (Typ_exist _,_) ->
            if alpha_equivalent env cast_typ ann_typ then false,false else true,true
         | Typ_aux (Typ_exist _,_), _ -> true,false
         | _, Typ_aux (Typ_exist _,_) -> false,true
         | _, _ -> false,false
       in
       let epp = if unpack then string "projT1" ^^ space ^^ parens epp else epp in
       let epp = if build_ex then string "build_ex" ^^ space ^^ parens epp else epp in
       if aexp_needed then parens epp else epp
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
       let recordtyp, env = match annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _)
           when Env.is_record tid env ->
           tid, env
         | _ ->  raise (report l ("cannot get record type from annot " ^ string_of_annot annot ^ " of exp " ^ string_of_exp full_exp)) in
       if List.length fexps > 1 then
         let _,fields = Env.get_record recordtyp env in
         let var, let_pp =
           match e with
           | E_aux (E_id id,_) -> id, empty
           | _ -> let v = mk_id "_record" in (* TODO: collision avoid *)
                  v, separate space [string "let "; doc_id v; coloneq; top_exp ctxt true e; string "in"] ^^ break 1
         in
         let doc_field (_,id) =
           match List.find (fun (FE_aux (FE_Fexp (id',_),_)) -> Id.compare id id' == 0) fexps with
           | fexp -> doc_fexp ctxt recordtyp fexp
           | exception Not_found ->
               let fname =
                 if prefix_recordtype && string_of_id recordtyp <> "regstate"
                 then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
                 else doc_id id in
               doc_op coloneq fname (doc_id var ^^ dot ^^ parens fname)
         in let_pp ^^ enclose_record (align (separate_map (semi_sp ^^ break 1)
                                               doc_field fields))
       else
         enclose_record_update (doc_op (string "with") (expY e) (separate_map semi_sp (doc_fexp ctxt recordtyp) fexps))
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
         else
           let vepp = string "vec_of_list_len" ^^ space ^^ align epp in
           (vepp,aexp_needed) in
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
                  (separate_map (break 1) (doc_case ctxt (typ_of e)) pexps) ^/^
                    (string "end")) in
       if aexp_needed then parens (align epp) else align epp
    | E_try (e, pexps) ->
       if effectful (effect_of e) then
         let try_catch = if ctxt.early_ret then "try_catchR" else "try_catch" in
         let epp =
           group ((separate space [string try_catch; expY e; string "(function "]) ^/^
                    (separate_map (break 1) (doc_case ctxt exc_typ) pexps) ^/^
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
       begin
         match pat, e1 with
         | (P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _)),
           (E_aux (E_assert (assert_e1,assert_e2),_)) ->
            let epp = liftR (separate space [string "assert_exp'"; expY assert_e1; expY assert_e2]) in
            let epp = infix 0 1 (string ">>= fun _ =>") epp (expN e2) in
            if aexp_needed then parens (align epp) else align epp
         | _ ->
            let epp =
              let b = match e1 with E_aux (E_if _,_) -> true | _ -> false in
              let middle =
                match fst (untyp_pat pat) with
                | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
                   string ">>"
                | P_aux (P_id id,_) ->
                   separate space [string ">>= fun"; doc_id id; bigarrow]
                | P_aux (P_typ (typ, P_aux (P_id id,_)),_) ->
                   separate space [string ">>= fun"; doc_id id; colon; doc_typ ctxt typ; bigarrow]
                | _ ->
                   separate space [string ">>= fun"; squote ^^ doc_pat ctxt true (pat, typ_of e1); bigarrow]
              in
              infix 0 1 middle (expV b e1) (expN e2)
            in
            if aexp_needed then parens (align epp) else epp
       end
    | E_internal_return (e1) ->
       wrap_parens (align (separate space [string "returnm"; expY e1]))
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
      (soft_surround 2 1 if_pp
         ((if condition_produces_constraint c then string "sumbool_of_bool" ^^ space else empty)
          ^^ parens (top_exp ctxt true c)) (string "then"))
      (top_exp ctxt false t)) ^^
    break 1 ^^
    else_pp
  and let_exp ctxt (LB_aux(lb,_)) = match lb with
    (* Prefer simple lets over patterns, because I've found Coq can struggle to
       work out return types otherwise *)
    | LB_val(P_aux (P_id id,_),e)
      when Util.is_none (is_auto_decomposed_exist (env_of e) (typ_of e)) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,P_aux (P_id id,_)),_),e)
      when Util.is_none (is_auto_decomposed_exist (env_of e) typ) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; colon; doc_typ ctxt typ; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,pat),_),(E_aux (_,e_ann) as e)) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true (pat, typ); coloneq])
              (top_exp ctxt false (E_aux (E_cast (typ,e),e_ann)))
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true (pat, typ_of e); coloneq])
              (top_exp ctxt false e)

  and doc_fexp ctxt recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype && string_of_id recordtyp <> "regstate"
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
      else doc_id id in
    group (doc_op coloneq fname (top_exp ctxt true e))

  and doc_case ctxt typ = function
  | Pat_aux(Pat_exp(pat,e),_) ->
    group (prefix 3 1 (separate space [pipe; doc_pat ctxt false (pat,typ);bigarrow])
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
       (separate space [string "Definition"; doc_id_type id;
                        doc_typquant_items empty_ctxt parens typq;
                        colon; string "Type"])
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
         let id_pp = doc_id_type id in
         let typ_nm = separate space [id_pp; doc_typquant_items empty_ctxt braces typq] in
         let ar_doc = group (separate_map (break 1 ^^ pipe ^^ space) (doc_type_union empty_ctxt id_pp) ar) in
         let typ_pp =
           (doc_op coloneq)
             (concat [string "Inductive"; space; typ_nm])
             ((*doc_typquant_lem typq*) ar_doc) in
         (* We declared the type parameters as implicit so that they're implicit
            in the constructors.  Currently Coq also makes them implicit in the
            type, so undo that here. *)
         let resetimplicit = separate space [string "Arguments"; id_pp; colon; string "clear implicits."] in
         typ_pp ^^ dot ^^ hardline ^^ resetimplicit ^^ hardline ^^ hardline)
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
         let id_pp = doc_id_type id in
         let typ_pp = (doc_op coloneq)
                        (concat [string "Inductive"; space; id_pp])
                        (enums_doc) in
         let eq1_pp = string "Scheme Equality for" ^^ space ^^ id_pp ^^ dot in
         let eq2_pp = string "Instance Decidable_eq_" ^^ id_pp ^^ space ^^ colon ^^ space ^^
           string "forall (x y : " ^^ id_pp ^^ string "), Decidable (x = y) :=" ^/^
           string "Decidable_eq_from_dec " ^^ id_pp ^^ string "_eq_dec." in
          typ_pp ^^ dot ^^ hardline ^^ eq1_pp ^^ hardline ^^ eq2_pp ^^ hardline)
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
  | P_tup pats, _ -> raise (Reporting_basic.err_unreachable l "Tuple pattern against non-tuple type")
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
    | P_aux (P_id id, ann), typ
    | P_aux (P_typ (_,P_aux (P_id id, ann)),_), typ -> begin
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
  let used_a_pattern = ref false in
  let doc_binder (P_aux (p,ann) as pat, typ) =
    let env = env_of_annot ann in
    let exp_typ = Env.expand_synonyms env typ in
    match p with
    | P_id id
    | P_typ (_,P_aux (P_id id,_)) when Util.is_none (is_auto_decomposed_exist env exp_typ) ->
       parens (separate space [doc_id id; colon; doc_typ ctxt typ])
    | _ ->
       (used_a_pattern := true;
        squote ^^ parens (separate space [doc_pat ctxt true (pat, exp_typ); colon; doc_typ ctxt typ]))
  in
  let patspp = separate_map space doc_binder pats in
  let atom_constrs = Util.map_filter (atom_constraint ctxt) pats in
  let atom_constr_pp = separate space atom_constrs in
  let retpp =
    if effectful eff
    then string "M" ^^ space ^^ parens (doc_typ ctxt ret_typ)
    else doc_typ ctxt ret_typ
  in
  let idpp = doc_id id in
  (* Work around Coq bug 7975 about pattern binders followed by implicit arguments *)
  let implicitargs =
    if !used_a_pattern && List.length constrspp + List.length atom_constrs > 0 then
      break 1 ^^ separate space
        ([string "Arguments"; idpp;] @
            List.map (fun _ -> string "{_}") quantspp @
            List.map (fun _ -> string "_") pats @
            List.map (fun _ -> string "{_}") constrspp @
            List.map (fun _ -> string "{_}") atom_constrs)
      ^^ dot
    else empty
  in
  let _ = match guard with
    | None -> ()
    | _ ->
       raise (Reporting_basic.err_unreachable l
                "guarded pattern expression should have been rewritten before pretty-printing") in
  group (prefix 3 1
    (separate space ([idpp] @ quantspp @ [patspp] @ constrspp @ [atom_constr_pp]) ^/^
       separate space [colon; retpp; coloneq])
    (doc_fun_body ctxt exp ^^ dot)) ^^ implicitargs

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

(* Remove some type variables in a similar fashion to merge_kids_atoms *)
let doc_axiom_typschm typ_env (TypSchm_aux (TypSchm_ts (tqs,typ),l) as ts) =
  let typ_env = add_typquant l tqs typ_env in
  match typ with
  | Typ_aux (Typ_fn (args_ty, ret_ty, eff),l') ->
     let check_typ (args,used) typ =
       match Type_check.destruct_atom_nexp typ_env typ with
       | Some (Nexp_aux (Nexp_var kid,_)) ->
          if KidSet.mem kid used then args,used else
            KidSet.add kid args, used
       | Some _ -> args, used
       | _ -> args, KidSet.union used (tyvars_of_typ typ)
     in
     let typs = match args_ty with Typ_aux (Typ_tup typs,_) -> typs | _ -> [args_ty] in
     let args, used = List.fold_left check_typ (KidSet.empty, KidSet.empty) typs in
     let used = if is_number ret_ty then used else KidSet.union used (tyvars_of_typ ret_ty) in
     let tqs = match tqs with
       | TypQ_aux (TypQ_tq qs,l) -> TypQ_aux (TypQ_tq (List.filter (function
         | QI_aux (QI_id kopt,_) when is_nat_kopt kopt ->
            let kid = kopt_kid kopt in
            KidSet.mem kid used && not (KidSet.mem kid args)
         | _ -> true) qs),l)
       | _ -> tqs
     in
     let doc_typ' typ =
       match Type_check.destruct_atom_nexp typ_env typ with
       | Some (Nexp_aux (Nexp_var kid,_)) when KidSet.mem kid args ->
          parens (doc_var_lem empty_ctxt kid ^^ string " : Z")
       | _ -> parens (underscore ^^ string " : " ^^ doc_typ empty_ctxt typ)
     in
     let arg_typs_pp = separate space (List.map doc_typ' typs) in
     let ret_typ_pp = doc_typ empty_ctxt ret_ty in
     let tyvars_pp, constrs_pp = doc_typquant_items_separate empty_ctxt braces tqs in
     string "forall" ^/^ separate space tyvars_pp ^/^
       arg_typs_pp ^/^ separate space constrs_pp ^^ comma ^/^ ret_typ_pp
  | _ -> doc_typschm empty_ctxt true ts

let doc_val_spec unimplemented (VS_aux (VS_val_spec(tys,id,_,_),ann)) =
  if !opt_undef_axioms && IdSet.mem id unimplemented then
    let typ_env = env_of_annot ann in
    group (separate space
             [string "Axiom"; doc_id id; colon; doc_axiom_typschm typ_env tys] ^^ dot) ^/^ hardline
  else empty (* Type signatures appear in definitions *)

(* If a top-level value is an existential type, we define the dependent pair of
   the value and the proof, then just the value with Let so that it appears in
   the local context when constraint solving and the ltac can find the proof. *)
let doc_val pat exp =
  let (id,typpp) = match pat with
    | P_aux (P_typ (typ, P_aux (P_id id,_)),_) -> id, space ^^ colon ^^ space ^^ doc_typ empty_ctxt typ
    | P_aux (P_id id, _) -> id, empty
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, empty
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, space ^^ colon ^^ space ^^ doc_typ empty_ctxt typ
    | _ -> raise (Reporting_basic.err_todo (pat_loc pat)
                    "Top-level value definition with complex pattern not supported for Coq yet")
  in
  let env = env_of exp in
  let typ = expand_range_type (Env.expand_synonyms env (typ_of exp)) in
  let id, opt_unpack =
    match destruct_exist env typ with
    | None -> id, None
    | Some (kids,nc,typ) ->
       match drop_duplicate_atoms kids typ, nc with
       | None, NC_aux (NC_true,_) -> id, None
       | _ ->
          (* TODO: name collisions *)
          mk_id (string_of_id id ^ "_spec"),
          Some (id, string_of_id id ^ "_prop")
  in
  let idpp = doc_id id in
  let basepp =
    group (string "Definition" ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^
             doc_exp_lem empty_ctxt false exp ^^ dot) ^^ hardline
  in
  match opt_unpack with
  | None -> basepp ^^ hardline
  | Some (orig_id, hyp_id) ->
     basepp ^^
       group (separate space [string "Let"; doc_id orig_id; coloneq; string "projT1"; idpp; dot]) ^^ hardline ^^ hardline

let rec doc_def unimplemented def =
  (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
  match def with
  | DEF_spec v_spec -> doc_val_spec unimplemented v_spec
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def -> group (doc_typdef t_def) ^/^ hardline
  | DEF_reg_dec dec -> group (doc_dec_lem dec)

  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec_lem fundefs ^/^ hardline
  | DEF_val (LB_aux (LB_val (pat, exp), _)) -> doc_val pat exp
  | DEF_scattered sdef -> failwith "doc_def: shoulnd't have DEF_scattered at this point"

  | DEF_kind _ -> empty

  | DEF_comm (DC_comm s) -> comment (string s)
  | DEF_comm (DC_comm_struct d) -> comment (doc_def unimplemented d)


let find_exc_typ defs =
  let is_exc_typ_def = function
    | DEF_type td -> string_of_id (id_of_type_def td) = "exception"
    | _ -> false in
  if List.exists is_exc_typ_def defs then "exception" else "unit"

let find_unimplemented defs =
  let adjust_def unimplemented = function
    | DEF_spec (VS_aux (VS_val_spec (_,id,ext,_),_)) -> begin
      match ext "coq" with
      | Some _ -> unimplemented
      | None -> IdSet.add id unimplemented
    end
    | DEF_fundef (FD_aux (FD_function (_,_,_,funcls),_)) -> begin
      match funcls with
      | [] -> unimplemented
      | (FCL_aux (FCL_Funcl (id,_),_))::_ ->
         IdSet.remove id unimplemented
    end
    | _ -> unimplemented
  in
  List.fold_left adjust_def IdSet.empty defs

let pp_defs_coq (types_file,types_modules) (defs_file,defs_modules) (Defs defs) top_line =
try
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
  let unimplemented = find_unimplemented defs in
  let () = if !opt_undef_axioms || IdSet.is_empty unimplemented then () else
      Reporting_basic.print_err false false Parse_ast.Unknown "Warning"
        ("The following functions were declared but are undefined:\n" ^
            String.concat "\n" (List.map string_of_id (IdSet.elements unimplemented)))
  in
  (print types_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) types_modules;hardline;
        separate empty (List.map (doc_def unimplemented) typdefs); hardline;
        hardline;
        separate empty (List.map (doc_def unimplemented) statedefs); hardline;
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
        string "Import ListNotations.";
        hardline;
        string "Open Scope string.";
        hardline;
        (* Put the body into a Section so that we can define some values with
           Let to put them into the local context, where tactics can see them *)
        string "Section Content.";
        hardline;
        hardline;
        separate empty (List.map (doc_def unimplemented) defs);
        hardline;
        string "End Content.";
        hardline])
with Type_check.Type_error (l,err) ->
  let extra =
    "\nError during Coq printing\n" ^
    if Printexc.backtrace_status ()
    then "\n" ^ Printexc.get_backtrace ()
    else "(backtracing unavailable)"
  in
  raise (Reporting_basic.err_typ l (Type_error.string_of_type_error err ^ extra))
