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
open Extra_pervasives

module StringSet = Set.Make(String)

let opt_undef_axioms = ref false
let opt_debug_on : string list ref = ref []

(****************************************************************************
 * PPrint-based sail-to-coq pprinter
****************************************************************************)

(* Data representation:
 *
 * In pure computations we keep values with top level existential types
 * (including ranges and nats) separate from the proofs of the accompanying
 * constraints, which keeps the terms shorter and more manageable.
 * Existentials embedded in types (e.g., in tuples or datatypes) are dependent
 * pairs.
 *
 * Monadic values always includes the proof in a dependent pair because the
 * constraint solving tactic won't see the term that defined the value, and
 * must rely entirely on the type (like the Sail type checker).
 *)


type context = {
  early_ret : bool;
  kid_renames : kid KBindings.t; (* Plain tyvar -> tyvar renames *)
  kid_id_renames : id KBindings.t; (* tyvar -> argument renames *)
  bound_nvars : KidSet.t;
  build_ex_return : bool;
  recursive_ids : IdSet.t;
  debug : bool;
}
let empty_ctxt = {
  early_ret = false;
  kid_renames = KBindings.empty;
  kid_id_renames = KBindings.empty;
  bound_nvars = KidSet.empty;
  build_ex_return = false;
  recursive_ids = IdSet.empty;
  debug = false;
}

let debug_depth = ref 0

let rec indent n = match n with
  | 0 -> ""
  | n -> "|   " ^ indent (n - 1)

let debug ctxt m =
  if ctxt.debug
  then print_endline (indent !debug_depth ^ Lazy.force m)
  else ()

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

let is_enum env id =
  match Env.lookup_id id env with
  | Enum _ -> true
  | _ -> false

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
  | "O"
  | "S"
  | "mod"
  | "M"
  | "tt"
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

let string_id (Id_aux(i,_)) =
  match i with
  | Id i -> fix_id false i
  | DeIid x -> Util.zencode_string ("op " ^ x)

let doc_id id = string (string_id id)

let doc_id_type (Id_aux(i,_)) =
  match i with
  | Id("int") -> string "Z"
  | Id("real") -> string "R"
  | Id i -> string (fix_id false i)
  | DeIid x -> string (Util.zencode_string ("op " ^ x))

let doc_id_ctor (Id_aux(i,_)) =
  match i with
  | Id i -> string (fix_id false i)
  | DeIid x -> string (Util.zencode_string ("op " ^ x))

let doc_var ctx kid =
  match KBindings.find kid ctx.kid_id_renames with
  | id -> doc_id id
  | exception Not_found ->
     string (fix_id true (string_of_kid (try KBindings.find kid ctx.kid_renames with Not_found -> kid)))

let doc_docstring (l, _) = match l with
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

let doc_nexp ctx ?(skip_vars=KidSet.empty) nexp =
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
        -> separate space [string "ZEuclid.div"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "mod",_), [n1;n2])
        -> separate space [string "ZEuclid.modulo"; atomic n1; atomic n2]
    | Nexp_app (Id_aux (Id "abs_atom",_), [n1])
        -> separate space [string "Z.abs"; atomic n1]
    | _ -> atomic nexp
  and atomic (Nexp_aux (n,l) as nexp) =
    match n with
    | Nexp_constant i -> string (Big_int.to_string i)
    | Nexp_var v when KidSet.mem v skip_vars -> string "_"
    | Nexp_var v -> doc_var ctx v
    | Nexp_id id -> doc_id id
    | Nexp_sum _ | Nexp_minus _ | Nexp_times _ | Nexp_neg _ | Nexp_exp _
    | Nexp_app (Id_aux (Id ("div"|"mod"),_), [_;_])
    | Nexp_app (Id_aux (Id "abs_atom",_), [_])
        -> parens (plussub nexp)
    | _ ->
       raise (Reporting.err_unreachable l __POS__
                ("cannot pretty-print nexp \"" ^ string_of_nexp nexp ^ "\""))
  in atomic nexp

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

(* Returns the set of type variables that will appear in the Coq output,
   which may be smaller than those in the Sail type.  May need to be
   updated with doc_typ *)
let rec coq_nvars_of_typ (Typ_aux (t,l)) =
  let trec = coq_nvars_of_typ in
  match t with
  | Typ_id _ -> KidSet.empty
  | Typ_var kid -> tyvars_of_nexp (orig_nexp (nvar kid))
  | Typ_fn (t1,t2,_) -> List.fold_left KidSet.union (trec t2) (List.map trec t1)
  | Typ_tup ts ->
     List.fold_left (fun s t -> KidSet.union s (trec t))
       KidSet.empty ts
  | Typ_app(Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) ->
     trec etyp
  | Typ_app(Id_aux (Id "implicit", _),_)
  (* TODO: update when complex atom types are sorted out *)
  | Typ_app(Id_aux (Id "atom", _), _) -> KidSet.empty
  | Typ_app (_,tas) ->
     List.fold_left (fun s ta -> KidSet.union s (coq_nvars_of_typ_arg ta))
       KidSet.empty tas
  (* TODO: remove appropriate bound variables *)
  | Typ_exist (_,_,t) -> trec t
  | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
and coq_nvars_of_typ_arg (A_aux (ta,_)) =
  match ta with
  | A_nexp nexp -> tyvars_of_nexp (orig_nexp nexp)
  | A_typ typ -> coq_nvars_of_typ typ
  | A_order _ -> KidSet.empty

(* Follows Coq precedence levels *)
let rec doc_nc_prop ctx nc =
  let rec l85 (NC_aux (nc,_) as nc_full) =
  match nc with
  | NC_or (nc1, nc2) -> doc_op (string "\\/") (doc_nc_prop ctx nc1) (doc_nc_prop ctx nc2)
  | _ -> l80 nc_full
  and l80 (NC_aux (nc,_) as nc_full) =
  match nc with
  | NC_and (nc1, nc2) -> doc_op (string "/\\") (doc_nc_prop ctx nc1) (doc_nc_prop ctx nc2)
  | _ -> l70 nc_full
  and l70 (NC_aux (nc,_) as nc_full) =
  match nc with
  | NC_equal (ne1, ne2) -> doc_op equals (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_bounded_ge (ne1, ne2) -> doc_op (string ">=") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_bounded_le (ne1, ne2) -> doc_op (string "<=") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | NC_not_equal (ne1, ne2) -> doc_op (string "<>") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
  | _ -> l10 nc_full
  and l10 (NC_aux (nc,_) as nc_full) =
  match nc with
  | NC_set (kid, is) ->
     separate space [string "In"; doc_var ctx kid;
                     brackets (separate (string "; ")
                                 (List.map (fun i -> string (Nat_big_num.to_string i)) is))]
  | NC_true -> string "True"
  | NC_false -> string "False"
  | NC_or _
  | NC_and _
  | NC_equal _
  | NC_bounded_ge _
  | NC_bounded_le _
  | NC_not_equal _ -> parens (l85 nc_full)
  in l85 nc

(* Follows Coq precedence levels *)
let doc_nc_exp ctx nc =
  let rec l70 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_equal (ne1, ne2) -> doc_op (string "=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_ge (ne1, ne2) -> doc_op (string ">=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | NC_bounded_le (ne1, ne2) -> doc_op (string "<=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2)
    | _ -> l50 nc_full
  and l50 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_or (nc1, nc2) -> doc_op (string "||") (l50 nc1) (l40 nc2)
    | _ -> l40 nc_full
  and l40 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_and (nc1, nc2) -> doc_op (string "&&") (l40 nc1) (l10 nc2)
    | _ -> l10 nc_full
  and l10 (NC_aux (nc,_) as nc_full) =
    match nc with
    | NC_not_equal (ne1, ne2) -> string "negb" ^^ space ^^ parens (doc_op (string "=?") (doc_nexp ctx ne1) (doc_nexp ctx ne2))
    | NC_set (kid, is) ->
       separate space [string "member_Z_list"; doc_var ctx kid;
                       brackets (separate (string "; ")
                                   (List.map (fun i -> string (Nat_big_num.to_string i)) is))]
    | NC_true -> string "true"
    | NC_false -> string "false"
    | NC_equal _
    | NC_bounded_ge _
    | NC_bounded_le _
    | NC_or _
    | NC_and _ -> parens (l70 nc_full)
  in l70 nc

let maybe_expand_range_type (Typ_aux (typ,l) as full_typ) =
  match typ with
  | Typ_app(Id_aux (Id "range", _), [A_aux(A_nexp low,_);
                                     A_aux(A_nexp high,_)]) ->
         (* TODO: avoid name clashes *)
     let kid = mk_kid "rangevar" in
     let var = nvar kid in
     let nc = nc_and (nc_lteq low var) (nc_lteq var high) in
     Some (Typ_aux (Typ_exist ([mk_kopt K_int kid], nc, atom_typ var),Parse_ast.Generated l))
  | Typ_id (Id_aux (Id "nat",_)) ->
     let kid = mk_kid "n" in
     let var = nvar kid in
     Some (Typ_aux (Typ_exist ([mk_kopt K_int kid], nc_gteq var (nconstant Nat_big_num.zero), atom_typ var),
                    Parse_ast.Generated l))
  | _ -> None

let expand_range_type typ = Util.option_default typ (maybe_expand_range_type typ)

let doc_arithfact ctxt ?(exists = []) ?extra nc =
  let prop = doc_nc_prop ctxt nc in
  let prop = match extra with
    | None -> prop
    | Some pp -> separate space [pp; string "/\\"; prop]
  in
  let prop =
    match exists with
    | [] -> prop
    | _ -> separate space ([string "exists"]@(List.map (doc_var ctxt) exists)@[comma; prop])
  in
  string "ArithFact" ^^ space ^^ parens prop

let nice_and nc1 nc2 =
match nc1, nc2 with
| NC_aux (NC_true,_), _ -> nc2
| _, NC_aux (NC_true,_) -> nc1
| _,_ -> nc_and nc1 nc2

(* When making changes here, check whether they affect coq_nvars_of_typ *)
let doc_typ, doc_atomic_typ =
  let fns ctx =
  (* following the structure of parser for precedence *)
  let rec typ ty = fn_typ true ty
    and typ' ty = fn_typ false ty
    and fn_typ atyp_needed ((Typ_aux (t, _)) as ty) = match t with
      | Typ_fn(args,ret,efct) ->
         let ret_typ =
           if effectful efct
           then separate space [string "M"; fn_typ true ret]
           else separate space [fn_typ false ret] in
         let arg_typs = List.map (app_typ false) args in
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
          A_aux (A_nexp m, _);
          A_aux (A_order ord, _);
          A_aux (A_typ elem_typ, _)]) ->
         (* TODO: remove duplication with exists, below *)
         let tpp = match elem_typ with
           | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) -> (* TODO: coq-compatible simplification *)
             string "mword " ^^ doc_nexp ctx m
           | _ -> string "vec" ^^ space ^^ typ elem_typ ^^ space ^^ doc_nexp ctx m in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "register", _), [A_aux (A_typ etyp, _)]) ->
         let tpp = string "register_ref regstate register_value " ^^ typ etyp in
         if atyp_needed then parens tpp else tpp
      | Typ_app(Id_aux (Id "range", _), _)
      | Typ_id (Id_aux (Id "nat", _)) ->
         (match maybe_expand_range_type ty with
         | Some typ -> atomic_typ atyp_needed typ
         | None -> raise (Reporting.err_unreachable l __POS__ "Bad range type"))
      | Typ_app(Id_aux (Id "implicit", _),_) ->
         (string "Z")
      | Typ_app(Id_aux (Id "atom", _), [A_aux(A_nexp n,_)]) ->
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
      | Typ_var v -> doc_var ctx v
      | Typ_app _ | Typ_tup _ | Typ_fn _ ->
         (* exhaustiveness matters here to avoid infinite loops
          * if we add a new Typ constructor *)
         let tpp = typ ty in
         if atyp_needed then parens tpp else tpp
      (* TODO: handle non-integer kopts *)
      | Typ_exist (kopts,nc,ty') -> begin
          let kopts,nc,ty' = match maybe_expand_range_type ty' with
            | Some (Typ_aux (Typ_exist (kopts',nc',ty'),_)) ->
               kopts'@kopts,nc_and nc nc',ty'
            | _ -> kopts,nc,ty'
          in
          match ty' with
          | Typ_aux (Typ_app (Id_aux (Id "atom",_),
                              [A_aux (A_nexp nexp,_)]),_) ->
             begin match nexp, kopts with
             | (Nexp_aux (Nexp_var kid,_)), [kopt] when Kid.compare kid (kopt_kid kopt) == 0 ->
                braces (separate space [doc_var ctx kid; colon; string "Z";
                                        ampersand; doc_arithfact ctx nc])
             | _ ->
                let var = mk_kid "_atom" in (* TODO collision avoid *)
                let nc = nice_and (nc_eq (nvar var) nexp) nc in
                braces (separate space [doc_var ctx var; colon; string "Z";
                                        ampersand; doc_arithfact ctx ~exists:(List.map kopt_kid kopts) nc])
             end
          | Typ_aux (Typ_app (Id_aux (Id "vector",_),
                              [A_aux (A_nexp m, _);
                               A_aux (A_order ord, _);
                               A_aux (A_typ elem_typ, _)]),_) ->
             (* TODO: proper handling of m, complex elem type, dedup with above *)
             let var = mk_kid "_vec" in (* TODO collision avoid *)
             let kid_set = KidSet.of_list (List.map kopt_kid kopts) in
             let m_pp = doc_nexp ctx ~skip_vars:kid_set m in
             let tpp, len_pp = match elem_typ with
               | Typ_aux (Typ_id (Id_aux (Id "bit",_)),_) ->
                  string "mword " ^^ m_pp, string "length_mword"
               | _ -> string "vec" ^^ space ^^ typ elem_typ ^^ space ^^ m_pp,
                      string "vec_length" in
             let length_constraint_pp =
               if KidSet.is_empty (KidSet.inter kid_set (nexp_frees m))
               then None
               else Some (separate space [len_pp; doc_var ctx var; equals; doc_nexp ctx m])
             in
             braces (separate space
                       [doc_var ctx var; colon; tpp;
                        ampersand;
                        doc_arithfact ctx ~exists:(List.map kopt_kid kopts) ?extra:length_constraint_pp nc])
          | _ ->
             raise (Reporting.err_todo l
                  ("Non-atom existential type not yet supported in Coq: " ^
                     string_of_typ ty))
        end

(*

        let add_tyvar tpp kid =
          braces (separate space [doc_var ctx kid; colon; string "Z"; ampersand; tpp])
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
        end*)
      | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
      | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"
    and doc_typ_arg (A_aux(t,_)) = match t with
      | A_typ t -> app_typ true t
      | A_nexp n -> doc_nexp ctx n
      | A_order o -> empty
  in typ', atomic_typ
  in (fun ctx -> (fst (fns ctx))), (fun ctx -> (snd (fns ctx)))

(* Check for variables in types that would be pretty-printed and are not
   bound in the val spec of the function. *)
let contains_t_pp_var ctxt (Typ_aux (t,a) as typ) =
  KidSet.subset (coq_nvars_of_typ typ) ctxt.bound_nvars

(* TODO: should we resurrect this?
let replace_typ_size ctxt env (Typ_aux (t,a)) =
  match t with
  | Typ_app (Id_aux (Id "vector",_) as id, [A_aux (A_nexp size,_);ord;typ']) ->
     begin
       let mk_typ nexp =
         Some (Typ_aux (Typ_app (id, [A_aux (A_nexp nexp,Parse_ast.Unknown);ord;typ']),a))
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
  | _ -> None*)

let doc_tannot ctxt env eff typ =
  let of_typ typ =
    let ta = doc_typ ctxt typ in
    if eff then
      if ctxt.early_ret
      then string " : MR " ^^ parens ta ^^ string " _"
      else string " : M " ^^ parens ta
    else string " : " ^^ ta
  in of_typ typ

(* Only double-quotes need escaped - by doubling them. *)
let coq_escape_string s =
  Str.global_replace (Str.regexp "\"") "\"\"" s
   
let doc_lit (L_aux(lit,l)) =
  match lit with
  | L_unit  -> utf8string "tt"
  | L_zero  -> utf8string "B0"
  | L_one   -> utf8string "B1"
  | L_false -> utf8string "false"
  | L_true  -> utf8string "true"
  | L_num i ->
     let s = Big_int.to_string i in
     let ipp = utf8string s in
     if Big_int.less i Big_int.zero then parens ipp else ipp
  | L_hex n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0x" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_bin n -> failwith "Shouldn't happen" (*"(num_to_vec " ^ ("0b" ^ n) ^ ")" (*shouldn't happen*)*)
  | L_undef ->
     utf8string "(Fail \"undefined value of unsupported type\")"
  | L_string s -> utf8string ("\"" ^ (coq_escape_string s) ^ "\"")
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
      raise (Reporting.Fatal_error
        (Reporting.Err_syntax_locn (l, "could not parse real literal"))) in
    parens (separate space (List.map string [
      "realFromFrac"; Big_int.to_string num; Big_int.to_string denom]))

let doc_quant_item_id ctx delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (K_aux (kind,_),kid),_)) -> begin
    if KBindings.mem kid ctx.kid_id_renames then None else
    match kind with
    | K_type -> Some (delimit (separate space [doc_var ctx kid; colon; string "Type"]))
    | K_int -> Some (delimit (separate space [doc_var ctx kid; colon; string "Z"]))
    | K_order -> None
  end
  | QI_const nc -> None

let quant_item_id_name ctx (QI_aux (qi,_)) =
  match qi with
  | QI_id (KOpt_aux (KOpt_kind (K_aux (kind,_),kid),_)) -> begin
    if KBindings.mem kid ctx.kid_id_renames then None else
    match kind with
    | K_type -> Some (doc_var ctx kid)
    | K_int -> Some (doc_var ctx kid)
    | K_order -> None
  end
  | QI_const nc -> None

let doc_quant_item_constr ctx delimit (QI_aux (qi,_)) =
  match qi with
  | QI_id  _ -> None
  | QI_const nc -> Some (bquote ^^ braces (doc_arithfact ctx nc))

(* At the moment these are all anonymous - when used we rely on Coq to fill
   them in. *)
let quant_item_constr_name ctx (QI_aux (qi,_)) =
  match qi with
  | QI_id  _ -> None
  | QI_const nc -> Some underscore

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

let typquant_names_separate ctx (TypQ_aux (tq,_)) =
  match tq with
  | TypQ_tq qis ->
     Util.map_filter (quant_item_id_name ctx) qis,
     Util.map_filter (quant_item_constr_name ctx) qis
  | TypQ_no_forall -> [], []


let doc_typquant ctx (TypQ_aux(tq,_)) typ = match tq with
| TypQ_tq ((_ :: _) as qs) ->
   string "forall " ^^ separate_opt space (doc_quant_item_id ctx braces) qs ^/^
     separate_opt space (doc_quant_item_constr ctx parens) qs ^^ string ", " ^^ typ
| _ -> typ

(* Produce Size type constraints for bitvector sizes when using
   machine words.  Often these will be unnecessary, but this simple
   approach will do for now. *)

let rec typeclass_nexps (Typ_aux(t,l)) =
  match t with
  | Typ_id _
  | Typ_var _
    -> NexpSet.empty
  | Typ_fn (t1,t2,_) -> List.fold_left NexpSet.union (typeclass_nexps t2) (List.map typeclass_nexps t1)
  | Typ_tup ts -> List.fold_left NexpSet.union NexpSet.empty (List.map typeclass_nexps ts)
  | Typ_app (Id_aux (Id "vector",_),
             [A_aux (A_nexp size_nexp,_);
              _;A_aux (A_typ (Typ_aux (Typ_id (Id_aux (Id "bit",_)),_)),_)])
  | Typ_app (Id_aux (Id "itself",_),
             [A_aux (A_nexp size_nexp,_)]) ->
     let size_nexp = nexp_simp size_nexp in
     if is_nexp_constant size_nexp then NexpSet.empty else
       NexpSet.singleton (orig_nexp size_nexp)
  | Typ_app _ -> NexpSet.empty
  | Typ_exist (kids,_,t) -> NexpSet.empty (* todo *)
  | Typ_bidir _ -> unreachable l __POS__ "Coq doesn't support bidir types"
  | Typ_internal_unknown -> unreachable l __POS__ "escaped Typ_internal_unknown"

let doc_typschm ctx quants (TypSchm_aux(TypSchm_ts(tq,t),_)) =
  let pt = doc_typ ctx t in
  if quants then doc_typquant ctx tq pt else pt

let is_ctor env id = match Env.lookup_id id env with
| Enum _ -> true
| _ -> false

let is_auto_decomposed_exist env typ =
  let typ = expand_range_type typ in
  match destruct_exist_plain (Env.expand_synonyms env typ) with
  | Some (_, _, typ') -> Some typ'
  | _ -> None

(*Note: vector concatenation, literal vectors, indexed vectors, and record should
  be removed prior to pp. The latter two have never yet been seen
*)
let rec doc_pat ctxt apat_needed exists_as_pairs (P_aux (p,(l,annot)) as pat, typ) =
  let env = env_of_annot (l,annot) in
  let typ = Env.expand_synonyms env typ in
  match exists_as_pairs, is_auto_decomposed_exist env typ with
  | true, Some typ' ->
     let pat_pp = doc_pat ctxt true true (pat, typ') in
     let pat_pp = separate space [string "existT"; underscore; pat_pp; underscore] in
     if apat_needed then parens pat_pp else pat_pp
  | _ ->
     match p with
     (* Special case translation of the None constructor to remove the unit arg *)
     | P_app(id, _) when string_of_id id = "None" -> string "None"
     | P_app(id, ((_ :: _) as pats)) -> begin
        (* Following the type checker to get the subpattern types, TODO perhaps ought
           to persuade the type checker to output these somehow. *)
       let (typq, ctor_typ) = Env.get_val_spec id env in
       let arg_typs =
         match Env.expand_synonyms env ctor_typ with
         | Typ_aux (Typ_fn (arg_typs, ret_typ, _), _) ->
            let unifiers = unify l env (tyvars_of_typ ret_typ) ret_typ typ in
            List.map (subst_unifiers unifiers) arg_typs
         | _ -> assert false
       in
       (* Constructors that were specified without a return type might get
          an extra tuple in their type; expand that here if necessary.
          TODO: this should go away if we enforce proper arities. *)
       let arg_typs = match pats, arg_typs with
         | _::_::_, [Typ_aux (Typ_tup typs,_)] -> typs
         | _,_ -> arg_typs
       in
       let ppp = doc_unop (doc_id_ctor id)
         (parens (separate_map comma (doc_pat ctxt true true) (List.combine pats arg_typs))) in
       if apat_needed then parens ppp else ppp
     end
     | P_app(id, []) -> doc_id_ctor id
     | P_lit lit  -> doc_lit lit
     | P_wild -> underscore
     | P_id id -> doc_id id
     | P_var(p,_) -> doc_pat ctxt true exists_as_pairs (p, typ)
     | P_as(p,id) -> parens (separate space [doc_pat ctxt true exists_as_pairs (p, typ); string "as"; doc_id id])
     | P_typ(ptyp,p) ->
        let doc_p = doc_pat ctxt true exists_as_pairs (p, typ) in
        doc_p
     (* Type annotations aren't allowed everywhere in patterns in Coq *)
     (*parens (doc_op colon doc_p (doc_typ typ))*)
     | P_vector pats ->
        let el_typ =
          match destruct_vector env typ with
          | Some (_,_,t) -> t
          | None -> raise (Reporting.err_unreachable l __POS__ "vector pattern doesn't have vector type")
        in
        let ppp = brackets (separate_map semi (fun p -> doc_pat ctxt true exists_as_pairs (p,el_typ)) pats) in
        if apat_needed then parens ppp else ppp
     | P_vector_concat pats ->
        raise (Reporting.err_unreachable l __POS__
                 "vector concatenation patterns should have been removed before pretty-printing")
     | P_tup pats  ->
        let typs = match typ with
          | Typ_aux (Typ_tup typs, _) -> typs
          | _ -> raise (Reporting.err_unreachable l __POS__ "tuple pattern doesn't have tuple type")
        in
        (match pats, typs with
        | [p], [typ'] -> doc_pat ctxt apat_needed true (p, typ')
        | [_], _ -> raise (Reporting.err_unreachable l __POS__ "tuple pattern length does not match tuple type length")
        | _ -> parens (separate_map comma_sp (doc_pat ctxt false true) (List.combine pats typs)))
     | P_list pats ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [A_aux (A_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting.err_unreachable l __POS__ "list pattern not a list")
        in
        brackets (separate_map semi (fun p -> doc_pat ctxt false true (p, el_typ)) pats)
     | P_cons (p,p') ->
        let el_typ = match typ with
          | Typ_aux (Typ_app (f, [A_aux (A_typ el_typ,_)]),_)
              when Id.compare f (mk_id "list") = 0 -> el_typ
          | _ -> raise (Reporting.err_unreachable l __POS__ "list pattern not a list")
        in
        doc_op (string "::") (doc_pat ctxt true true (p, el_typ)) (doc_pat ctxt true true (p', typ))
     | P_string_append _ -> unreachable l __POS__
        "string append pattern found in Coq backend, should have been rewritten"
     | P_not _ -> unreachable l __POS__ "Coq backend doesn't support not patterns"
     | P_or _ -> unreachable l __POS__ "Coq backend doesn't support or patterns yet"
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
  | Typ_app (register, [A_aux (A_typ (Typ_aux (Typ_id id, _)), _)])
    when string_of_id register = "register" -> id
  | Typ_app (id, _) -> id
  | _ -> raise (Reporting.err_unreachable l __POS__ "failed to get type id")

(* TODO: maybe Nexp_exp, division? *)
(* Evaluation of constant nexp subexpressions, because Coq will be able to do those itself *)
let rec nexp_const_eval (Nexp_aux (n,l) as nexp) =
  let binop f re l n1 n2 =
  match nexp_const_eval n1, nexp_const_eval n2 with
  | Nexp_aux (Nexp_constant c1,_), Nexp_aux (Nexp_constant c2,_) ->
     Nexp_aux (Nexp_constant (f c1 c2),l)
  | n1', n2' -> Nexp_aux (re n1' n2',l)
  in
  let unop f re l n1 =
  match nexp_const_eval n1 with
  | Nexp_aux (Nexp_constant c1,_) -> Nexp_aux (Nexp_constant (f c1),l)
  | n1' -> Nexp_aux (re n1',l)
  in
  match n with
  | Nexp_times (n1,n2) -> binop Big_int.mul (fun n1 n2 -> Nexp_times (n1,n2)) l n1 n2
  | Nexp_sum (n1,n2) -> binop Big_int.add (fun n1 n2 -> Nexp_sum (n1,n2)) l n1 n2
  | Nexp_minus (n1,n2) -> binop Big_int.sub (fun n1 n2 -> Nexp_minus (n1,n2)) l n1 n2
  | Nexp_neg n1 -> unop Big_int.negate (fun n -> Nexp_neg n) l n1
  | _ -> nexp

(* Decide whether two nexps used in a vector size are similar; if not
   a cast will be inserted *)
let similar_nexps ctxt env n1 n2 =
  let rec same_nexp_shape (Nexp_aux (n1,_)) (Nexp_aux (n2,_)) =
    match n1, n2 with
    | Nexp_id _, Nexp_id _ -> true
    (* TODO: this is really just an approximation to what we really want:
       will the Coq types have the same names?  We could probably do better
       by tracking which existential kids are equal to bound kids. *)
    | Nexp_var k1, Nexp_var k2 ->
       Kid.compare k1 k2 == 0 ||
         (prove env (nc_eq (nvar k1) (nvar k2)) && (
            not (KidSet.mem k1 ctxt.bound_nvars) ||
              not (KidSet.mem k2 ctxt.bound_nvars)))
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
  in if same_nexp_shape (nexp_const_eval n1) (nexp_const_eval n2) then true else false

let constraint_fns = ["Z.leb"; "Z.geb"; "Z.ltb"; "Z.gtb"; "Z.eqb"; "neq_atom"]

let condition_produces_constraint exp =
  (* Cheat a little - this isn't quite the right environment for subexpressions
     but will have all of the relevant functions in it. *)
  let env = env_of exp in
  Rewriter.fold_exp
    { (Rewriter.pure_exp_alg false (||)) with
      Rewriter.e_app = fun (f,bs) ->
        List.exists (fun x -> x) bs ||
        (let name = if Env.is_extern f env "coq"
          then Env.get_extern f env "coq"
          else string_id f in
         List.exists (fun id -> String.compare name id == 0) constraint_fns)
    } exp

(* For most functions whose return types are non-trivial atoms we return a
   dependent pair with a proof that the result is the expected integer.  This
   is redundant for basic arithmetic functions and functions which we unfold
   in the constraint solver. *)
let no_Z_proof_fns = ["Z.add"; "Z.sub"; "Z.opp"; "Z.mul"; "length_mword"; "length"]

let is_no_Z_proof_fn env id =
  if Env.is_extern id env "coq"
  then
    let s = Env.get_extern id env "coq" in
    List.exists (fun x -> String.compare x s == 0) no_Z_proof_fns
  else false

let replace_atom_return_type ret_typ =
  (* TODO: more complex uses of atom *)
  match ret_typ with
  | Typ_aux (Typ_app (Id_aux (Id "atom",_), [A_aux (A_nexp nexp,_)]),l) ->
     let kid = mk_kid "_retval" in (* TODO: collision avoidance *)
     true, Typ_aux (Typ_exist ([mk_kopt K_int kid], nc_eq (nvar kid) nexp, atom_typ (nvar kid)),Parse_ast.Generated l)
  | _ -> false, ret_typ

let is_range_from_atom env (Typ_aux (argty,_)) (Typ_aux (fnty,_)) =
  match argty, fnty with
  | Typ_app(Id_aux (Id "atom", _), [A_aux (A_nexp nexp,_)]),
    Typ_app(Id_aux (Id "range", _), [A_aux(A_nexp low,_);
                                     A_aux(A_nexp high,_)]) ->
     Type_check.prove env (nc_and (nc_eq nexp low) (nc_eq nexp high))
  | _ -> false

(* Get a more general type for an annotation/expression - i.e.,
   like typ_of but using the expected type if there was one *)
let general_typ_of_annot annot =
  match expected_typ_of annot with
  | None -> typ_of_annot annot
  | Some typ -> typ

let general_typ_of (E_aux (_,annot)) = general_typ_of_annot annot

let is_prefix s s' =
  let l = String.length s in
  String.length s' >= l &&
  String.sub s' 0 l = s

let prefix_recordtype = true
let report = Reporting.err_unreachable
let doc_exp, doc_let =
  let rec top_exp (ctxt : context) (aexp_needed : bool)
    (E_aux (e, (l,annot)) as full_exp) =
    let top_exp c a e = 
      let () = debug_depth := !debug_depth + 1 in
      let r = top_exp c a e in
      let () = debug_depth := !debug_depth - 1 in
      r
    in
    let expY = top_exp ctxt true in
    let expN = top_exp ctxt false in
    let expV = top_exp ctxt in
    let wrap_parens doc = if aexp_needed then parens (doc) else doc in
    let maybe_add_exist epp =
      let env = env_of full_exp in
      let typ = Env.expand_synonyms env (general_typ_of full_exp) in
      let () =
        debug ctxt (lazy ("Considering build_ex for " ^ string_of_exp full_exp));
        debug ctxt (lazy (" at type " ^ string_of_typ typ))
      in
      let typ = expand_range_type typ in
      match destruct_exist_plain typ with
      | None -> epp
      | Some _ ->
         let epp = string "build_ex" ^/^ epp in
         if aexp_needed then parens epp else epp
    in
    let rec construct_dep_pairs env =
      let rec aux want_parens (E_aux (e,_) as exp) (Typ_aux (t,_) as typ) =
        match e,t with
        | E_tuple exps, Typ_tup typs
        | E_cast (_, E_aux (E_tuple exps,_)), Typ_tup typs
          ->
           parens (separate (string ", ") (List.map2 (aux false) exps typs))
        | _ ->
           let typ' = expand_range_type (Env.expand_synonyms (env_of exp) typ) in
           let build_ex, out_typ =
             match destruct_exist_plain typ' with
             | Some (_,_,t) -> true, t
             | None -> false, typ'
           in
           let in_typ = expand_range_type (Env.expand_synonyms (env_of exp) (typ_of exp)) in
           let in_typ = match destruct_exist_plain in_typ with Some (_,_,t) -> t | None -> in_typ in
           let autocast =
             (* Avoid using helper functions which simplify the nexps *)
             is_bitvector_typ in_typ && is_bitvector_typ out_typ &&
               match in_typ, out_typ with
               | Typ_aux (Typ_app (_,[A_aux (A_nexp n1,_);_;_]),_),
                 Typ_aux (Typ_app (_,[A_aux (A_nexp n2,_);_;_]),_) ->
                  not (similar_nexps ctxt (env_of exp) n1 n2)
               | _ -> false
           in
           let exp_pp = expV (want_parens || autocast || build_ex) exp in
           let exp_pp =
             if autocast then
               let exp_pp = string "autocast" ^^ space ^^ exp_pp in
               if want_parens || build_ex then parens exp_pp else exp_pp
             else exp_pp
           in if build_ex then
                let exp_pp = string "build_ex" ^^ space ^^ exp_pp in
                if want_parens then parens exp_pp else exp_pp
              else exp_pp
      in aux
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
                 raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
                 liftR ((prefix 2 1)
                   (string "write_reg_field_range")
                   (align (doc_lexp_deref ctxt le ^/^
                      field_ref ^/^ expY e2 ^/^ expY e3 ^/^ expY e)))
            | _ ->
               let deref = doc_lexp_deref ctxt le in
               liftR ((prefix 2 1)
                 (string "write_reg_range")
                 (align (deref ^/^ expY e2 ^/^ expY e3) ^/^ expY e)))
        | LEXP_vector (le,e2) ->
           (match le with
            | LEXP_aux (LEXP_field ((LEXP_aux (_, lannot) as le),id), fannot) ->
               if is_bit_typ (typ_of_annot fannot) then
                 raise (report l __POS__ "indexing a register's (single bit) bitfield not supported")
               else
                 let field_ref =
                   doc_id (typ_id_of (typ_of_annot lannot)) ^^
                   underscore ^^
                   doc_id id in
                 let call = if is_bitvector_typ (Env.base_typ_of (env_of full_exp) (typ_of_annot fannot)) then "write_reg_field_bit" else "write_reg_field_pos" in
                 liftR ((prefix 2 1)
                   (string call)
                   (align (doc_lexp_deref ctxt le ^/^
                     field_ref ^/^ expY e2 ^/^ expY e)))
            | LEXP_aux (_, lannot) ->
               let deref = doc_lexp_deref ctxt le in
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
             (doc_lexp_deref ctxt le ^^ space ^^
                field_ref ^/^ expY e))
        | LEXP_deref re ->
           liftR ((prefix 2 1) (string "write_reg") (expY re ^/^ expY e))
        | _ ->
           liftR ((prefix 2 1) (string "write_reg") (doc_lexp_deref ctxt le ^/^ expY e)))
    | E_vector_append(le,re) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_append should have been rewritten before pretty-printing")
    | E_cons(le,re) -> doc_op (group (colon^^colon)) (expY le) (expY re)
    | E_if(c,t,e) ->
       let epp = if_exp ctxt false c t e in
       if aexp_needed then parens (align epp) else epp
    | E_for(id,exp1,exp2,exp3,(Ord_aux(order,_)),exp4) ->
       raise (report l __POS__ "E_for should have been rewritten before pretty-printing")
    | E_loop _ ->
       raise (report l __POS__ "E_loop should have been rewritten before pretty-printing")
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
                 | _ -> raise (Reporting.err_unreachable l __POS__ ("Unable to find loop variable in " ^ string_of_exp body)) in
               let dir = match ord_exp with
                 | E_aux (E_lit (L_aux (L_false, _)), _) -> "_down"
                 | E_aux (E_lit (L_aux (L_true, _)), _) -> "_up"
                 | _ -> raise (Reporting.err_unreachable l __POS__ ("Unexpected loop direction " ^ string_of_exp ord_exp))
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
                      separate space [string "let"; squote ^^ expY vartuple; string ":= varstup in"]
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
          | _ -> raise (Reporting.err_unreachable l __POS__
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
                      separate space [string "let"; squote ^^ expY varstuple; string ":= varstup in"]
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
            | _ -> raise (Reporting.err_unreachable l __POS__
               "Unexpected number of arguments for loop combinator")
          end
       | Id_aux (Id "early_return", _) ->
          begin
            match args with
            | [exp] ->
               let exp_pp =
                 if ctxt.build_ex_return
                 then parens (string "build_ex" ^/^ expY exp)
                 else expY exp
               in
               let epp = separate space [string "early_return"; exp_pp] in
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
            | _ -> raise (Reporting.err_unreachable l __POS__
               "Unexpected number of arguments for early_return builtin")
          end
       | _ ->
          let env = env_of_annot (l,annot) in
          let () = debug ctxt (lazy ("Function application " ^ string_of_id f)) in
          let call, is_extern, is_ctor, is_rec =
            if Env.is_union_constructor f env then doc_id_ctor f, false, true, false else
            if Env.is_extern f env "coq"
            then string (Env.get_extern f env "coq"), true, false, false
            else if IdSet.mem f ctxt.recursive_ids
            then doc_id f, false, false, true
            else doc_id f, false, false, false in
          let (tqs,fn_ty) = Env.get_val_spec f env in
          (* Calculate the renaming *)
          let tqs_map = List.fold_left
                          (fun m k ->
                            let kid = kopt_kid k in
                            KBindings.add (orig_kid kid) kid m)
                          KBindings.empty (quant_kopts tqs) in
          let arg_typs, ret_typ, eff = match fn_ty with
            | Typ_aux (Typ_fn (arg_typs,ret_typ,eff),_) -> arg_typs, ret_typ, eff
            | _ -> raise (Reporting.err_unreachable l __POS__ "Function not a function type")
          in
          let inst =
            (* We attempt to get an instantiation of the function signature's
               type variables which agrees with Coq by
               1. using dummy variables with the expected type of each argument
                  (avoiding the inferred type, which might have (e.g.) stripped
                  out an existential quantifier)
               2. calculating the instantiation without using the expected
                  return type, so that we can work out if we need a cast around
                  the function call. *)
            let dummy_args =
              Util.list_mapi (fun i exp -> mk_id ("#coq#arg" ^ string_of_int i),
                                           general_typ_of exp) args
            in
            let dummy_exp = mk_exp (E_app (f, List.map (fun (id,_) -> mk_exp (E_id id)) dummy_args)) in
            let dummy_env = List.fold_left (fun env (id,typ) -> Env.add_local id (Immutable,typ) env) env dummy_args in
            let inst_exp =
              try infer_exp dummy_env dummy_exp
              with ex ->
                debug ctxt (lazy (" cannot infer dummy application " ^ Printexc.to_string ex));
                full_exp
            in
            match instantiation_of_without_type inst_exp with
            | x -> x
            (* Not all function applications can be inferred, so try falling back to the
               type inferred when we know the target type.
               TODO: there are probably some edge cases where this won't pick up a need
               to cast. *)
            | exception _ -> instantiation_of full_exp
          in
          let inst = KBindings.fold (fun k u m -> KBindings.add (KBindings.find (orig_kid k) tqs_map) u m) inst KBindings.empty in
          let () = debug ctxt (lazy (" instantiations: " ^ String.concat ", " (List.map (fun (kid,tyarg) -> string_of_kid kid ^ " => " ^ string_of_typ_arg tyarg) (KBindings.bindings inst)))) in

          (* Insert existential packing of arguments where necessary *)
          let doc_arg want_parens arg typ_from_fn =
            let env = env_of arg in
            let typ_from_fn = subst_unifiers inst typ_from_fn in
            let typ_from_fn = Env.expand_synonyms env typ_from_fn in
            (* TODO: more sophisticated check *)
            let () =
              debug ctxt (lazy (" arg type found    " ^ string_of_typ (typ_of arg)));
              debug ctxt (lazy (" arg type expected " ^ string_of_typ typ_from_fn))
            in
            let typ_of_arg = Env.expand_synonyms env (typ_of arg) in
            let typ_of_arg = expand_range_type typ_of_arg in
            let typ_of_arg' = match typ_of_arg with Typ_aux (Typ_exist (_,_,t),_) -> t  | t -> t in
            let typ_from_fn' = match typ_from_fn with Typ_aux (Typ_exist (_,_,t),_) -> t  | t -> t in
            let autocast =
              (* Avoid using helper functions which simplify the nexps *)
              is_bitvector_typ typ_of_arg' && is_bitvector_typ typ_from_fn' &&
              match typ_of_arg', typ_from_fn' with
              | Typ_aux (Typ_app (_,[A_aux (A_nexp n1,_);_;_]),_),
                Typ_aux (Typ_app (_,[A_aux (A_nexp n2,_);_;_]),_) ->
                 not (similar_nexps ctxt env n1 n2)
              | _ -> false
            in
            (* If the argument is an integer that can be inferred from the
               context in a different form, let Coq fill it in.  E.g.,
               when "64" is really "8 * width".  Avoid cases where the
               type checker has introduced a phantom type variable while
               calculating the instantiations. *)
            let vars_in_env n =
              let ekids = Env.get_typ_vars env in
              KidSet.for_all (fun kid -> KBindings.mem kid ekids) (nexp_frees n)
            in
            match typ_of_arg, typ_from_fn with
            | Typ_aux (Typ_app (Id_aux (Id "atom",_),[A_aux (A_nexp n1,_)]),_),
              Typ_aux (Typ_app (Id_aux (Id "atom",_),[A_aux (A_nexp n2,_)]),_)
                 when vars_in_env n2 && not (similar_nexps ctxt env n1 n2) ->
               underscore
            | _ ->
               let want_parens1 = want_parens || autocast in
               let arg_pp =
                 construct_dep_pairs env want_parens1 arg typ_from_fn
               in
               if autocast && false
               then let arg_pp = string "autocast" ^^ space ^^ arg_pp in
                    if want_parens then parens arg_pp else arg_pp
               else arg_pp
          in
          let epp =
            if is_ctor
            then hang 2 (call ^^ break 1 ^^ parens (flow (comma ^^ break 1) (List.map2 (doc_arg false) args arg_typs)))
            else
              let main_call = call :: List.map2 (doc_arg true) args arg_typs in
              let all =
                if is_rec then main_call @
                                 [parens (string "_limit_reduces _acc")]
                else match f with
                     | Id_aux (Id x,_) when is_prefix "#rec#" x ->
                        main_call @ [parens (string "Zwf_guarded _")]
                     | _ ->  main_call
              in hang 2 (flow (break 1) all) in

          (* Decide whether to unpack an existential result, pack one, or cast.
             To do this we compare the expected type stored in the checked expression
             with the inferred type. *)
          let ret_typ_inst =
               subst_unifiers inst ret_typ
          in
          let packeff,unpack,autocast =
            let ann_typ = Env.expand_synonyms env (general_typ_of_annot (l,annot)) in
            let ann_typ = expand_range_type ann_typ in
            let ret_typ_inst = expand_range_type (Env.expand_synonyms env ret_typ_inst) in
            let ret_typ_inst =
              if is_no_Z_proof_fn env f then ret_typ_inst
              else snd (replace_atom_return_type ret_typ_inst) in
            let () = 
              debug ctxt (lazy (" type returned " ^ string_of_typ ret_typ_inst));
              debug ctxt (lazy (" type expected " ^ string_of_typ ann_typ))
            in
            let unpack, in_typ =
              match ret_typ_inst with
              | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
              | t1 -> false,t1
            in
            let pack,out_typ = 
              match ann_typ with
              | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
              | t1 -> false,t1
            in
            let autocast =
              (* Avoid using helper functions which simplify the nexps *)
              is_bitvector_typ in_typ && is_bitvector_typ out_typ &&
              match in_typ, out_typ with
              | Typ_aux (Typ_app (_,[A_aux (A_nexp n1,_);_;_]),_),
                Typ_aux (Typ_app (_,[A_aux (A_nexp n2,_);_;_]),_) ->
                 not (similar_nexps ctxt env n1 n2)
              | _ -> false
            in pack,unpack,autocast
          in
          let autocast_id, proj_id =
            if effectful eff
            then "autocast_m", "projT1_m"
            else "autocast",   "projT1" in
          let epp = if unpack && not (effectful eff) then string proj_id ^^ space ^^ parens epp else epp in
          let epp = if autocast then string autocast_id ^^ space ^^ parens epp else epp in
          let epp =
            if effectful eff && packeff && not unpack
            then string "build_ex_m" ^^ space ^^ parens epp
            else epp
          in
          liftR (if aexp_needed then parens (align epp) else epp)
       end
    | E_vector_access (v,e) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_access should have been rewritten before pretty-printing")
    | E_vector_subrange (v,e1,e2) ->
      raise (Reporting.err_unreachable l __POS__
        "E_vector_subrange should have been rewritten before pretty-printing")
    | E_field((E_aux(_,(l,fannot)) as fexp),id) ->
       (match destruct_tannot fannot with
        | Some(env, (Typ_aux (Typ_id tid, _)), _)
        | Some(env, (Typ_aux (Typ_app (tid, _), _)), _)
          when Env.is_record tid env ->
           let fname =
             if prefix_recordtype && string_of_id tid <> "regstate"
             then (string (string_of_id tid ^ "_")) ^^ doc_id id
             else doc_id id in
           expY fexp ^^ dot ^^ parens fname
        | _ ->
           raise (report l __POS__ "E_field expression with no register or record type"))
    | E_block [] -> string "tt"
    | E_block exps -> raise (report l __POS__ "Blocks should have been removed till now.")
    | E_nondet exps -> raise (report l __POS__ "Nondet blocks not supported.")
    | E_id id | E_ref id ->
       let env = env_of full_exp in
       let typ = typ_of full_exp in
       let eff = effect_of full_exp in
       let base_typ = Env.base_typ_of env typ in
       if has_effect eff BE_rreg then
         let epp = separate space [string "read_reg";doc_id (append_id id "_ref")] in
         if is_bitvector_typ base_typ
         then wrap_parens (align (group (prefix 0 1 (parens (liftR epp)) (doc_tannot ctxt env true base_typ))))
         else liftR epp
       else if Env.is_register id env then doc_id (append_id id "_ref")
       else if is_ctor env id then doc_id_ctor id
       else begin
         match Env.lookup_id id env with
         | Local (_,typ) ->
            let exp_typ = expand_range_type (Env.expand_synonyms env typ) in
            let ann_typ = general_typ_of full_exp in
            let ann_typ = expand_range_type (Env.expand_synonyms env ann_typ) in
            let () =
              debug ctxt (lazy ("Variable " ^ string_of_id id ^ " with type " ^ string_of_typ typ));
              debug ctxt (lazy (" expected type " ^ string_of_typ ann_typ))
            in
            doc_id id
         | _ -> doc_id id
       end
    | E_lit lit -> doc_lit lit
    | E_cast(typ,e) ->
       let epp = expV true e in
       let env = env_of_annot (l,annot) in
       let outer_typ = Env.expand_synonyms env (general_typ_of_annot (l,annot)) in
       let outer_typ = expand_range_type outer_typ in
       let cast_typ = expand_range_type (Env.expand_synonyms env typ) in
       let inner_typ = Env.expand_synonyms env (general_typ_of e) in
       let inner_typ = expand_range_type inner_typ in
       let () =
         debug ctxt (lazy ("Cast of type " ^ string_of_typ cast_typ));
         debug ctxt (lazy (" on expr of type " ^ string_of_typ inner_typ));
         debug ctxt (lazy (" where type expected is " ^ string_of_typ outer_typ))
       in
       let outer_ex,outer_typ' =
         match outer_typ with
         | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
         | t1 -> false,t1
       in
       let cast_ex,cast_typ' =
         match cast_typ with
         | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
         | t1 -> false,t1
       in
       let inner_ex,inner_typ' =
         match inner_typ with
         | Typ_aux (Typ_exist (_,_,t1),_) -> true,t1
         | t1 -> false,t1
       in
       let autocast =
                (* Avoid using helper functions which simplify the nexps *)
         is_bitvector_typ outer_typ' && is_bitvector_typ cast_typ' &&
           match outer_typ', cast_typ' with
           | Typ_aux (Typ_app (_,[A_aux (A_nexp n1,_);_;_]),_),
         Typ_aux (Typ_app (_,[A_aux (A_nexp n2,_);_;_]),_) ->
              not (similar_nexps ctxt env n1 n2)
           | _ -> false
       in
       let effects = effectful (effect_of e) in
       let epp =
         if effects then
           if inner_ex then
             if cast_ex
             (* If the types are the same use the cast as a hint to Coq,
                otherwise derive the new type from the old one. *)
             then if alpha_equivalent env inner_typ cast_typ
                  then epp
                  else string "derive_m" ^^ space ^^ epp
             else string "projT1_m" ^^ space ^^ epp
           else if cast_ex
           then string "build_ex_m" ^^ space ^^ epp
           else epp
         else if cast_ex
         then string "build_ex" ^^ space ^^ epp
         else epp
       in
       let epp = epp ^/^ doc_tannot ctxt (env_of e) effects typ in
       let epp =
         if effects then
           if cast_ex && not outer_ex
           then string "projT1_m" ^^ space ^^ parens epp
           else epp
         else if cast_ex
         then string "projT1" ^^ space ^^ parens epp
         else epp
       in
       let epp =
         if autocast then
           string (if effects then "autocast_m" else "autocast") ^^ space ^^ parens epp
         else epp
       in
       if aexp_needed then parens epp else epp
    | E_tuple exps ->
       construct_dep_pairs (env_of_annot (l,annot)) true full_exp (general_typ_of full_exp)
    | E_record fexps ->
       let recordtyp = match destruct_tannot annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _) ->
           (* when Env.is_record tid env -> *)
           tid
         | _ ->  raise (report l __POS__ ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)) in
       let epp = enclose_record (align (separate_map
                                          (semi_sp ^^ break 1)
                                          (doc_fexp ctxt recordtyp) fexps)) in
       if aexp_needed then parens epp else epp
    | E_record_update(e, fexps) ->
       let recordtyp, env = match destruct_tannot annot with
         | Some (env, Typ_aux (Typ_id tid,_), _)
         | Some (env, Typ_aux (Typ_app (tid, _), _), _)
           when Env.is_record tid env ->
           tid, env
         | _ ->  raise (report l __POS__ ("cannot get record type from annot " ^ string_of_tannot annot ^ " of exp " ^ string_of_exp full_exp)) in
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
         else raise (Reporting.err_unreachable l __POS__
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
           (align (group (prefix 0 1 bepp (doc_tannot ctxt (env_of full_exp) false t))), true)
         else
           let vepp = string "vec_of_list_len" ^^ space ^^ align epp in
           (vepp,aexp_needed) in
       if aexp_needed then parens (align epp) else epp
    | E_vector_update(v,e1,e2) ->
       raise (Reporting.err_unreachable l __POS__
         "E_vector_update should have been rewritten before pretty-printing")
    | E_vector_update_subrange(v,e1,e2,e3) ->
       raise (Reporting.err_unreachable l __POS__
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
           (* TODO capture avoidance for __catch_val *)
           group ((separate space [string try_catch; expY e; string "(fun __catch_val => match __catch_val with "]) ^/^
                    (separate_map (break 1) (doc_case ctxt exc_typ) pexps) ^/^
                      (string "end)")) in
         if aexp_needed then parens (align epp) else align epp
       else
         raise (Reporting.err_todo l "Warning: try-block around pure expression")
    | E_throw e ->
       let epp = liftR (separate space [string "throw"; expY e]) in
       if aexp_needed then parens (align epp) else align epp
    | E_exit e -> liftR (separate space [string "exit"; expY e])
    | E_assert (e1,e2) ->
       let epp = liftR (separate space [string "assert_exp"; expY e1; expY e2]) in
       if aexp_needed then parens (align epp) else align epp
    | E_app_infix (e1,id,e2) ->
       raise (Reporting.err_unreachable l __POS__
         "E_app_infix should have been rewritten before pretty-printing")
    | E_var(lexp, eq_exp, in_exp) ->
       raise (report l __POS__ "E_vars should have been removed before pretty-printing")
    | E_internal_plet (pat,e1,e2) ->
       begin
         let () =
           debug ctxt (lazy ("Internal plet, pattern " ^ string_of_pat pat));
           debug ctxt (lazy (" type of e1 " ^ string_of_typ (typ_of e1)))
         in
         match pat, e1, e2 with
         | (P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _)),
           (E_aux (E_assert (assert_e1,assert_e2),_)), _ ->
            let epp = liftR (separate space [string "assert_exp'"; expY assert_e1; expY assert_e2]) in
            let epp = infix 0 1 (string ">>= fun _ =>") epp (expN e2) in
            if aexp_needed then parens (align epp) else align epp
         (* Special case because we don't handle variables with nested existentials well yet.
            TODO: check that id1 is not used in e2' *)
         | ((P_aux (P_id id1,_)) | P_aux (P_typ (_, P_aux (P_id id1,_)),_)),
           _,
           (E_aux (E_let (LB_aux (LB_val (pat', E_aux (E_cast (typ', E_aux (E_id id2,_)),_)),_), e2'),_))
             when Id.compare id1 id2 == 0 ->
            let m_str, tail_pp = if ctxt.early_ret then "MR",[string "_"] else "M",[] in
            let e1_pp = parens (separate space ([expY e1; colon;
                                                string m_str;
                                                parens (doc_typ ctxt typ')]@tail_pp)) in
            let middle =
              match pat' with
              | P_aux (P_id id,_)
                   when Util.is_none (is_auto_decomposed_exist (env_of e1) (typ_of e1)) &&
                          not (is_enum (env_of e1) id) ->
                 separate space [string ">>= fun"; doc_id id; bigarrow]
              | P_aux (P_typ (typ, P_aux (P_id id,_)),_)
                   when Util.is_none (is_auto_decomposed_exist (env_of e1) typ) &&
                          not (is_enum (env_of e1) id) ->
                 separate space [string ">>= fun"; doc_id id; colon; doc_typ ctxt typ; bigarrow]              | _ ->
                 separate space [string ">>= fun"; squote ^^ doc_pat ctxt true true (pat', typ'); bigarrow]
            in
            infix 0 1 middle e1_pp (expN e2')
         | _ ->
            let epp =
              let middle =
                match pat with
                | P_aux (P_wild,_) | P_aux (P_typ (_, P_aux (P_wild, _)), _) ->
                   string ">>"
                | P_aux (P_id id,_)
                   when Util.is_none (is_auto_decomposed_exist (env_of e1) (typ_of e1)) &&
                        not (is_enum (env_of e1) id) ->
                   separate space [string ">>= fun"; doc_id id; bigarrow]
                | P_aux (P_typ (typ, P_aux (P_id id,_)),_)
                   when Util.is_none (is_auto_decomposed_exist (env_of e1) typ) &&
                        not (is_enum (env_of e1) id) ->
                   separate space [string ">>= fun"; doc_id id; colon; doc_typ ctxt typ; bigarrow]
                | P_aux (P_typ (typ, P_aux (P_id id,_)),_)
                | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id,_),_),_)),_)
                | P_aux (P_var (P_aux (P_typ (typ, P_aux (P_id id,_)),_),_),_)
                    when not (is_enum (env_of e1) id) ->
                      let full_typ = (expand_range_type typ) in
                      let binder = match destruct_exist_plain (Env.expand_synonyms (env_of e1) full_typ) with
                        | Some _ ->
                           squote ^^ parens (separate space [string "existT"; underscore; doc_id id; underscore; colon; doc_typ ctxt typ])
                        | _ ->
                           parens (separate space [doc_id id; colon; doc_typ ctxt typ])
                      in separate space [string ">>= fun"; binder; bigarrow]
                | _ ->
                   separate space [string ">>= fun"; squote ^^ doc_pat ctxt true true (pat, typ_of e1); bigarrow]
              in
              infix 0 1 middle (expY e1) (expN e2)
            in
            if aexp_needed then parens (align epp) else epp
       end
    | E_internal_return (e1) ->
       let exp_typ = typ_of e1 in
       let ret_typ = general_typ_of full_exp in
       let () =
         debug ctxt (lazy ("Monad return of " ^ string_of_exp e1));
         debug ctxt (lazy (" with type " ^ string_of_typ exp_typ));
         debug ctxt (lazy (" at type " ^ string_of_typ ret_typ))
       in
       let valpp =
         let env = env_of e1 in
         construct_dep_pairs env true e1 ret_typ
       in
       wrap_parens (align (separate space [string "returnm"; valpp]))
    | E_sizeof nexp ->
      (match nexp_simp nexp with
        | Nexp_aux (Nexp_constant i, _) -> doc_lit (L_aux (L_num i, l))
        | _ ->
          raise (Reporting.err_unreachable l __POS__
            "pretty-printing non-constant sizeof expressions to Lem not supported"))
    | E_return r ->
      let ret_monad = " : MR" in
      let exp_pp =
        if ctxt.build_ex_return
        then parens (string "build_ex" ^/^ expY r)
        else expY r
      in
      let ta =
        if contains_t_pp_var ctxt (typ_of full_exp) || contains_t_pp_var ctxt (typ_of r)
        then empty
        else separate space
          [string ret_monad;
          parens (doc_typ ctxt (typ_of full_exp));
          parens (doc_typ ctxt (typ_of r))] in
      align (parens (string "early_return" ^//^ exp_pp ^//^ ta))
    | E_constraint nc -> wrap_parens (doc_nc_exp ctxt nc)
    | E_internal_value _ ->
      raise (Reporting.err_unreachable l __POS__
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
      when Util.is_none (is_auto_decomposed_exist (env_of e) (typ_of e)) &&
           not (is_enum (env_of e) id) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,P_aux (P_id id,_)),_),e)
      when Util.is_none (is_auto_decomposed_exist (env_of e) typ) &&
           not (is_enum (env_of e) id) ->
       prefix 2 1
              (separate space [string "let"; doc_id id; colon; doc_typ ctxt typ; coloneq])
              (top_exp ctxt false e)
    | LB_val(P_aux (P_typ (typ,pat),_),(E_aux (_,e_ann) as e)) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true false (pat, typ); coloneq])
              (top_exp ctxt false (E_aux (E_cast (typ,e),e_ann)))
    | LB_val(pat,e) ->
       prefix 2 1
              (separate space [string "let"; squote ^^ doc_pat ctxt true false (pat, typ_of e); coloneq])
              (top_exp ctxt false e)

  and doc_fexp ctxt recordtyp (FE_aux(FE_Fexp(id,e),_)) =
    let fname =
      if prefix_recordtype && string_of_id recordtyp <> "regstate"
      then (string (string_of_id recordtyp ^ "_")) ^^ doc_id id
      else doc_id id in
    group (doc_op coloneq fname (top_exp ctxt true e))

  and doc_case ctxt typ = function
  | Pat_aux(Pat_exp(pat,e),_) ->
    group (prefix 3 1 (separate space [pipe; doc_pat ctxt false false (pat,typ);bigarrow])
                  (group (top_exp ctxt false e)))
  | Pat_aux(Pat_when(_,_,_),(l,_)) ->
    raise (Reporting.err_unreachable l __POS__
     "guarded pattern expression should have been rewritten before pretty-printing")

  and doc_lexp_deref ctxt ((LEXP_aux(lexp,(l,annot)))) = match lexp with
    | LEXP_field (le,id) ->
       parens (separate empty [doc_lexp_deref ctxt le;dot;doc_id id])
    | LEXP_id id -> doc_id (append_id id "_ref")
    | LEXP_cast (typ,id) -> doc_id (append_id id "_ref")
    | LEXP_tup lexps -> parens (separate_map comma_sp (doc_lexp_deref ctxt) lexps)
    | _ ->
       raise (Reporting.err_unreachable l __POS__ ("doc_lexp_deref: Unsupported lexp"))
             (* expose doc_exp and doc_let *)
  in top_exp, let_exp

(* FIXME: A temporary definition of List.init until 4.06 is more standard *)
let list_init n f = Array.to_list (Array.init n f)

let types_used_with_generic_eq defs =
  let rec add_typ idset (Typ_aux (typ,_)) =
    match typ with
    | Typ_id id -> IdSet.add id idset
    | Typ_app (id,args) ->
       List.fold_left add_typ_arg (IdSet.add id idset) args
    | Typ_tup ts -> List.fold_left add_typ idset ts
    | _ -> idset
  and add_typ_arg idset (A_aux (ta,_)) =
    match ta with
    | A_typ typ -> add_typ idset typ
    | _ -> idset
  in
  let alg =
    { (Rewriter.compute_exp_alg IdSet.empty IdSet.union) with
      Rewriter.e_aux = fun ((typs,exp),annot) ->
        let typs' =
          match exp with
          | E_app (f,[arg1;_]) ->
             if Env.is_extern f (env_of_annot annot) "coq" then
               let f' = Env.get_extern f (env_of_annot annot) "coq" in
               if f' = "generic_eq" || f' = "generic_neq" then
                 add_typ typs (Env.expand_synonyms (env_of arg1) (typ_of arg1))
               else typs
             else typs
          | _ -> typs
        in typs', E_aux (exp,annot) }
  in
  let typs_req_funcl (FCL_aux (FCL_Funcl (_,pexp), _)) =
    fst (Rewriter.fold_pexp alg pexp)
  in
  let typs_req_def = function
    | DEF_kind _
    | DEF_type _
    | DEF_spec _
    | DEF_fixity _
    | DEF_overload _
    | DEF_default _
    | DEF_pragma _
    | DEF_reg_dec _
      -> IdSet.empty
    | DEF_fundef (FD_aux (FD_function (_,_,_,fcls),_)) ->
       List.fold_left IdSet.union IdSet.empty (List.map typs_req_funcl fcls)
    | DEF_mapdef (MD_aux (_,(l,_)))
    | DEF_scattered (SD_aux (_,(l,_)))
      -> unreachable l __POS__ "Internal definition found in the Coq back-end"
    | DEF_internal_mutrec _
      -> unreachable Unknown __POS__ "Internal definition found in the Coq back-end"
    | DEF_val lb ->
       fst (Rewriter.fold_letbind alg lb)
  in
  List.fold_left IdSet.union IdSet.empty (List.map typs_req_def defs)

let doc_type_union ctxt typ_name (Tu_aux(Tu_ty_id(typ,id),_)) =
  separate space [doc_id_ctor id; colon;
                  doc_typ ctxt typ; arrow; typ_name]

let rec doc_range (BF_aux(r,_)) = match r with
  | BF_single i -> parens (doc_op comma (doc_int i) (doc_int i))
  | BF_range(i1,i2) -> parens (doc_op comma (doc_int i1) (doc_int i2))
  | BF_concat(ir1,ir2) -> (doc_range ir1) ^^ comma ^^ (doc_range ir2)

let doc_typdef generic_eq_types (TD_aux(td, (l, annot))) = match td with
  | TD_abbrev(id,typq,A_aux (A_typ typ, _)) ->
     let typschm = TypSchm_aux (TypSchm_ts (typq, typ), l) in
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
          | QI_aux (QI_id (KOpt_aux (KOpt_kind (_, kid), _)), l) ->
            [A_aux (A_nexp (Nexp_aux (Nexp_var kid, l)), l)]
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
    let id_pp = doc_id_type id in
    let numfields = List.length fs in
    let intros_pp s =
      string " intros [" ^^
      separate space (list_init numfields (fun n -> string (s ^ string_of_int n))) ^^
      string "]." ^^ hardline
    in
    let eq_pp =
      if IdSet.mem id generic_eq_types then
        string "Instance Decidable_eq_" ^^ id_pp ^^ space ^^ colon ^/^
        string "forall (x y : " ^^ id_pp ^^ string "), Decidable (x = y)." ^^
        hardline ^^ intros_pp "x" ^^ intros_pp "y" ^^
        separate hardline (list_init numfields
                             (fun n ->
                               let ns = string_of_int n in
                               string ("cmp_record_field x" ^ ns ^ " y" ^ ns ^ "."))) ^^
        hardline ^^
        string "refine (Build_Decidable _ true _). subst. split; reflexivity." ^^ hardline ^^
        string "Defined." ^^ hardline
      else empty
    in
    doc_op coloneq
           (separate space [string "Record"; id_pp; doc_typquant_items empty_ctxt parens typq])
           ((*doc_typquant typq*) (braces (space ^^ align fs_doc ^^ space))) ^^
      dot ^^ hardline ^^ eq_pp ^^ updates_pp
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
             ((*doc_typquant typq*) ar_doc) in
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
         let eq2_pp = string "Instance Decidable_eq_" ^^ id_pp ^^ space ^^ colon ^/^
           string "forall (x y : " ^^ id_pp ^^ string "), Decidable (x = y) :=" ^/^
           string "Decidable_eq_from_dec " ^^ id_pp ^^ string "_eq_dec." in
          typ_pp ^^ dot ^^ hardline ^^ eq1_pp ^^ hardline ^^ eq2_pp ^^ hardline)
    | _ -> raise (Reporting.err_unreachable l __POS__ "register with non-constant indices")

let args_of_typ l env typs =
  let arg i typ =
    let id = mk_id ("arg" ^ string_of_int i) in
    (P_aux (P_id id, (l, mk_tannot env typ no_effect)), typ),
    E_aux (E_id id, (l, mk_tannot env typ no_effect)) in
  List.split (List.mapi arg typs)

(* Sail currently has a single pattern to match against a list of
   argument types.  We need to tweak everything to match up,
   especially so that the function is presented in curried form.  In
   particular, if there's a single binder for multiple arguments
   (which rewriting can currently introduce) then we need to turn it
   into multiple binders and reconstruct it in the function body. *)
let rec untuple_args_pat typs (P_aux (paux, ((l, _) as annot)) as pat) =
  let env = env_of_annot annot in
  let identity = (fun body -> body) in
  match paux, typs with
  | P_tup [], _ ->
     let annot = (l, mk_tannot Env.empty unit_typ no_effect) in
     [P_aux (P_lit (mk_lit L_unit), annot), unit_typ], identity
  | P_tup pats, _ -> List.combine pats typs, identity
  | P_wild, _ ->
     let wild typ = P_aux (P_wild, (l, mk_tannot env typ no_effect)), typ in
     List.map wild typs, identity
  | P_typ (_, pat), _ -> untuple_args_pat typs pat
  | P_as _, _::_::_ | P_id _, _::_::_ ->
     let argpats, argexps = args_of_typ l env typs in
     let argexp = E_aux (E_tuple argexps, annot) in
     let bindargs (E_aux (_, bannot) as body) =
       E_aux (E_let (LB_aux (LB_val (pat, argexp), annot), body), bannot) in
     argpats, bindargs
  | _, [typ] ->
     [pat,typ], identity
  | _, _ ->
     unreachable l __POS__ "Unexpected pattern/type combination"

let doc_fun_body ctxt exp =
  let doc_exp = doc_exp ctxt false exp in
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

let pat_is_plain_binder env (P_aux (p,_)) =
  match p with
  | P_id id
  | P_typ (_,P_aux (P_id id,_))
  when not (is_enum env id) -> Some id
  | _ -> None

let demote_all_patterns env i (P_aux (p,p_annot) as pat,typ) =
  match pat_is_plain_binder env pat with
  | Some id ->
     if Util.is_none (is_auto_decomposed_exist env typ)
     then (pat,typ), fun e -> e
     else
       (P_aux (P_id id, p_annot),typ),
       fun (E_aux (_,e_ann) as e) ->
       E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)
  | None ->
    let id = mk_id ("arg" ^ string_of_int i) in (* TODO: name conflicts *)
    (P_aux (P_id id, p_annot),typ),
    fun (E_aux (_,e_ann) as e) ->
      E_aux (E_let (LB_aux (LB_val (pat, E_aux (E_id id, p_annot)),p_annot),e),e_ann)

(* Add equality constraints between arguments and nexps, except in the case
   that they've been merged. *)

let rec atom_constraint ctxt (pat, typ) =
  let typ = Env.base_typ_of (env_of_pat pat) typ in
  match pat, typ with
  | P_aux (P_id id, _),
      Typ_aux (Typ_app (Id_aux (Id "atom",_),
                        [A_aux (A_nexp nexp,_)]),_) ->
     (match nexp with
       (* When the kid is mapped to the id, we don't need a constraint *)
     | Nexp_aux (Nexp_var kid,_)
         when (try Id.compare (KBindings.find kid ctxt.kid_id_renames) id == 0 with _ -> false) ->
           None
     | _ ->
        Some (bquote ^^ braces (string "ArithFact" ^^ space ^^
                                  parens (doc_op equals (doc_id id) (doc_nexp ctxt nexp)))))
  | P_aux (P_typ (_,p),_), _ -> atom_constraint ctxt (p, typ)
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
             Reporting.print_err false true l "merge_kids_atoms"
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


let merge_var_patterns map pats =
  let map,pats = List.fold_left (fun (map,pats) (pat, typ) ->
    match pat with
    | P_aux (P_var (P_aux (P_id id,_), TP_aux (TP_var kid,_)),ann) ->
       KBindings.add kid id map, (P_aux (P_id id,ann), typ) :: pats
    | _ -> map, (pat,typ)::pats) (map,[]) pats
  in map, List.rev pats

let doc_funcl rec_opt (FCL_aux(FCL_Funcl(id, pexp), annot)) =
  let env = env_of_annot annot in
  let (tq,typ) = Env.get_val_spec_orig id env in
  let (arg_typs, ret_typ, eff) = match typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ, eff),_) -> arg_typs, ret_typ, eff
    | _ -> failwith ("Function " ^ string_of_id id ^ " does not have function type")
  in
  let build_ex, ret_typ = replace_atom_return_type ret_typ in
  let build_ex = match destruct_exist_plain (Env.expand_synonyms env (expand_range_type ret_typ)) with
    | Some _ -> true
    | _ -> build_ex
  in
  let ids_to_avoid = all_ids pexp in
  let bound_kids = tyvars_of_typquant tq in
  let pat,guard,exp,(l,_) = destruct_pexp pexp in
  let pats, bind = untuple_args_pat arg_typs pat in
  (* Fixpoint definitions can only use simple binders, but even Definitions
     can't handle as patterns *)
  let pattern_elim =
    match rec_opt with
    | Rec_aux (Rec_nonrec,_) -> demote_as_pattern
    | _ -> demote_all_patterns env
  in
  let pats, binds = List.split (Util.list_mapi pattern_elim pats) in
  let eliminated_kids, kid_to_arg_rename = merge_kids_atoms pats in
  let kid_to_arg_rename, pats = merge_var_patterns kid_to_arg_rename pats in
  let kids_used = KidSet.diff bound_kids eliminated_kids in
  let is_measured, recursive_ids = match rec_opt with
    (* No mutual recursion in this backend yet; only change recursive
       definitions where we have a measure *)
    | Rec_aux (Rec_measure _,_) -> true, IdSet.singleton id
    | _ -> false, IdSet.empty
  in
  let ctxt =
    { early_ret = contains_early_return exp;
      kid_renames = mk_kid_renames ids_to_avoid kids_used;
      kid_id_renames = kid_to_arg_rename;
      bound_nvars = bound_kids;
      build_ex_return = effectful eff && build_ex;
      recursive_ids = recursive_ids;
      debug = List.mem (string_of_id id) (!opt_debug_on)
    } in
  let () =
    debug ctxt (lazy ("Function " ^ string_of_id id));
    debug ctxt (lazy (" return type " ^ string_of_typ ret_typ));
    debug ctxt (lazy (" build_ex " ^ if build_ex then "needed" else "not needed"));
    debug ctxt (lazy (if effectful eff then " effectful" else " pure"))
  in
  (* Put the constraints after pattern matching so that any type variable that's
     been replaced by one of the term-level arguments is bound. *)
  let quantspp, constrspp = doc_typquant_items_separate ctxt braces tq in
  let exp = List.fold_left (fun body f -> f body) (bind exp) binds in
  let used_a_pattern = ref false in
  let doc_binder (P_aux (p,ann) as pat, typ) =
    let env = env_of_annot ann in
    let exp_typ = Env.expand_synonyms env typ in
    let () =
      debug ctxt (lazy (" pattern " ^ string_of_pat pat));
      debug ctxt (lazy (" with expanded type " ^ string_of_typ exp_typ))
    in
    match pat_is_plain_binder env pat with
    | Some id ->
       if Util.is_none (is_auto_decomposed_exist env exp_typ) then
         parens (separate space [doc_id id; colon; doc_typ ctxt typ])
       else begin
           let full_typ = (expand_range_type exp_typ) in
           match destruct_exist_plain (Env.expand_synonyms env full_typ) with
           | Some ([kopt], NC_aux (NC_true,_),
                   Typ_aux (Typ_app (Id_aux (Id "atom",_),
                                     [A_aux (A_nexp (Nexp_aux (Nexp_var kid,_)),_)]),_))
               when Kid.compare (kopt_kid kopt) kid == 0 ->
              parens (separate space [doc_id id; colon; string "Z"])
           | Some ([kopt], nc,
                   Typ_aux (Typ_app (Id_aux (Id "atom",_),
                                     [A_aux (A_nexp (Nexp_aux (Nexp_var kid,_)),_)]),_))
               when Kid.compare (kopt_kid kopt) kid == 0 && not is_measured ->
              (used_a_pattern := true;
               squote ^^ parens (separate space [string "existT"; underscore; doc_id id; underscore; colon; doc_typ ctxt typ]))
           | _ ->
              parens (separate space [doc_id id; colon; doc_typ ctxt typ])
         end
    | None ->
       (used_a_pattern := true;
        squote ^^ parens (separate space [doc_pat ctxt true true (pat, exp_typ); colon; doc_typ ctxt typ]))
  in
  let patspp = flow_map (break 1) doc_binder pats in
  let atom_constrs = Util.map_filter (atom_constraint ctxt) pats in
  let atom_constr_pp = separate space atom_constrs in
  let retpp =
    if effectful eff
    then string "M" ^^ space ^^ parens (doc_typ ctxt ret_typ)
    else doc_typ ctxt ret_typ
  in
  let idpp = doc_id id in
  let intropp, accpp, measurepp, fixupspp = match rec_opt with
    | Rec_aux (Rec_measure _,_) ->
       let fixupspp =
         Util.map_filter (fun (pat,typ) ->
             match pat_is_plain_binder env pat with
             | Some id -> begin
                 match destruct_exist_plain (Env.expand_synonyms env (expand_range_type typ)) with
                 | Some (_, NC_aux (NC_true,_), _) -> None
                 | Some ([KOpt_aux (KOpt_kind (_, kid), _)], nc,
                         Typ_aux (Typ_app (Id_aux (Id "atom",_),
                           [A_aux (A_nexp (Nexp_aux (Nexp_var kid',_)),_)]),_))
                      when Kid.compare kid kid' == 0 ->
                    Some (string "let " ^^ doc_id id ^^ string " := projT1 " ^^ doc_id id ^^ string " in")
                 | _ -> None
               end
             | None -> None) pats
       in
       string "Fixpoint",
       [parens (string "_acc : Acc (Zwf 0) _reclimit")],
       [string "{struct _acc}"],
       fixupspp
    | Rec_aux (r,_) ->
       let d = match r with Rec_nonrec -> "Definition" | _ -> "Fixpoint" in
       string d, [], [], []
  in
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
       raise (Reporting.err_unreachable l __POS__
               "guarded pattern expression should have been rewritten before pretty-printing") in
  let bodypp = doc_fun_body ctxt exp in
  let bodypp = if effectful eff || not build_ex then bodypp else string "build_ex" ^^ parens bodypp in
  let bodypp = separate (break 1) fixupspp ^/^ bodypp in
  group (prefix 3 1
    (flow (break 1) ([intropp; idpp] @ quantspp @ [patspp] @ constrspp @ [atom_constr_pp] @ accpp) ^/^
       flow (break 1) (measurepp @ [colon; retpp; coloneq]))
    (bodypp ^^ dot)) ^^ implicitargs

let get_id = function
  | [] -> failwith "FD_function with empty list"
  | (FCL_aux (FCL_Funcl (id,_),_))::_ -> id

(* Strictly speaking, Lem doesn't support multiple clauses for a single function
   joined by "and", although it has worked for Isabelle before.  However, all
   the funcls should have been merged by the merge_funcls rewrite now. *)   
let doc_fundef_rhs (FD_aux(FD_function(r, typa, efa, funcls),fannot)) =
  separate_map (hardline ^^ string "and ") (doc_funcl r) funcls

let doc_mutrec = function
  | [] -> failwith "DEF_internal_mutrec with empty function list"
  | fundefs ->
     string "let rec " ^^
     separate_map (hardline ^^ string "and ") doc_fundef_rhs fundefs

let rec doc_fundef (FD_aux(FD_function(r, typa, efa, fcls),fannot)) =
  match fcls with
  | [] -> failwith "FD_function with empty function list"
  | [FCL_aux (FCL_Funcl(id,_),annot) as funcl]
    when not (Env.is_extern id (env_of_annot annot) "coq") ->
     doc_funcl r funcl
  | [_] -> empty (* extern *)
  | _ -> failwith "FD_function with more than one clause"



let doc_dec (DEC_aux (reg, ((l, _) as annot))) =
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
         else raise (Reporting.err_unreachable l __POS__ ("can't deal with register type " ^ string_of_typ typ))
       else raise (Reporting.err_unreachable l __POS__ ("can't deal with register type " ^ string_of_typ typ)) *)
  | DEC_config _ -> empty
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
    | _ -> raise (Reporting.err_typ Parse_ast.Unknown
       ("Non-constant indices in register type " ^ tname)) in
  let dir_b = i1 < i2 in
  let dir = (if dir_b then "true" else "false") in
  let doc_field (fr, fid) =
    let i, j = match fr with
    | BF_aux (BF_single i, _) -> (i, i)
    | BF_aux (BF_range (i, j), _) -> (i, j)
    | _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__
        ("Unsupported type in field " ^ string_of_id fid ^ " of " ^ tname)) in
    let fsize = Big_int.succ (Big_int.abs (Big_int.sub i j)) in
    (* TODO Assumes normalised, decreasing bitvector slices; however, since
       start indices or indexing order do not appear in Lem type annotations,
       this does not matter. *)
    let ftyp = vector_typ (nconstant fsize) dec_ord bit_typ in
    let reftyp =
      mk_typ (Typ_app (Id_aux (Id "field_ref", Parse_ast.Unknown),
        [mk_typ_arg (A_typ (mk_id_typ (mk_id tname)));
         mk_typ_arg (A_typ ftyp)])) in
    let rfannot = doc_tannot empty_ctxt Env.empty false reftyp in
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
  | Typ_aux (Typ_fn (typs, ret_ty, eff),l') ->
     let check_typ (args,used) typ =
       match Type_check.destruct_atom_nexp typ_env typ with
       | Some (Nexp_aux (Nexp_var kid,_)) ->
          if KidSet.mem kid used then args,used else
            KidSet.add kid args, used
       | Some _ -> args, used
       | _ -> args, KidSet.union used (tyvars_of_typ typ)
     in
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
          parens (doc_var empty_ctxt kid ^^ string " : Z")
       | _ -> parens (underscore ^^ string " : " ^^ doc_typ empty_ctxt typ)
     in
     let arg_typs_pp = separate space (List.map doc_typ' typs) in
     let _, ret_ty = replace_atom_return_type ret_ty in
     let ret_typ_pp = doc_typ empty_ctxt ret_ty in
     let ret_typ_pp =
       if effectful eff
       then string "M" ^^ space ^^ parens ret_typ_pp
       else ret_typ_pp
     in
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

(* If a top-level value is declared with an existential type, we turn it into
   a type annotation expression instead (unless it duplicates an existing one). *)
let doc_val pat exp =
  let (id,pat_typ) = match pat with
    | P_aux (P_typ (typ, P_aux (P_id id,_)),_) -> id, Some typ
    | P_aux (P_id id, _) -> id, None
    | P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, None
    | P_aux (P_typ (typ, P_aux (P_var (P_aux (P_id id, _), TP_aux (TP_var kid, _)),_)),_) when Id.compare id (id_of_kid kid) == 0 ->
       id, Some typ
    | _ -> raise (Reporting.err_todo (pat_loc pat)
                    "Top-level value definition with complex pattern not supported for Coq yet")
  in
  let typpp = match pat_typ with
    | None -> empty
    | Some typ -> space ^^ colon ^^ space ^^ doc_typ empty_ctxt typ
  in
  let env = env_of exp in
  let ctxt = { empty_ctxt with debug  = List.mem (string_of_id id) (!opt_debug_on) } in
  let typpp, exp =
    match pat_typ with
    | None -> typpp, exp
    | Some typ ->
       let typ = expand_range_type (Env.expand_synonyms env typ) in
       match destruct_exist_plain typ with
       | None -> typpp, exp
       | Some _ ->
          empty, match exp with
          | E_aux (E_cast (typ',_),_) when alpha_equivalent env typ typ' -> exp
          | _ -> E_aux (E_cast (typ,exp), (Parse_ast.Unknown, mk_tannot env typ (effect_of exp)))
  in
  let idpp = doc_id id in
  let base_pp = doc_exp ctxt false exp ^^ dot in
  group (string "Definition" ^^ space ^^ idpp ^^ typpp ^^ space ^^ coloneq ^/^ base_pp) ^^ hardline ^^
  group (separate space [string "Hint Unfold"; idpp; colon; string "sail."]) ^^ hardline

let rec doc_def unimplemented generic_eq_types def =
  (* let _ = Pretty_print_sail.pp_defs stderr (Defs [def]) in *)
  match def with
  | DEF_spec v_spec -> doc_val_spec unimplemented v_spec
  | DEF_fixity _ -> empty
  | DEF_overload _ -> empty
  | DEF_type t_def -> group (doc_typdef generic_eq_types t_def) ^/^ hardline
  | DEF_reg_dec dec -> group (doc_dec dec)

  | DEF_default df -> empty
  | DEF_fundef fdef -> group (doc_fundef fdef) ^/^ hardline
  | DEF_internal_mutrec fundefs -> doc_mutrec fundefs ^/^ hardline
  | DEF_val (LB_aux (LB_val (pat, exp), _)) -> doc_val pat exp
  | DEF_scattered sdef -> failwith "doc_def: shoulnd't have DEF_scattered at this point"
  | DEF_mapdef (MD_aux (_, (l,_))) -> unreachable l __POS__ "Coq doesn't support mappings"
  | DEF_kind _ -> empty
  | DEF_pragma _ -> empty

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
  let generic_eq_types = types_used_with_generic_eq defs in
  let doc_def = doc_def unimplemented generic_eq_types in
  let () = if !opt_undef_axioms || IdSet.is_empty unimplemented then () else
      Reporting.print_err false false Parse_ast.Unknown "Warning"
        ("The following functions were declared but are undefined:\n" ^
            String.concat "\n" (List.map string_of_id (IdSet.elements unimplemented)))
  in
  (print types_file)
    (concat
       [string "(*" ^^ (string top_line) ^^ string "*)";hardline;
        (separate_map hardline)
          (fun lib -> separate space [string "Require Import";string lib] ^^ dot) types_modules;hardline;
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
        string "Import ListNotations.";
        hardline;
        string "Open Scope string."; hardline;
        string "Open Scope bool."; hardline;
        (* Put the body into a Section so that we can define some values with
           Let to put them into the local context, where tactics can see them *)
        string "Section Content.";
        hardline;
        hardline;
        separate empty (List.map doc_def defs);
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
  raise (Reporting.err_typ l (Type_error.string_of_type_error err ^ extra))
