(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Ast
open Ast_defs
open Ast_util
open Util
open Lazy

module Big_int = Nat_big_num

(* opt_tc_debug controls the verbosity of the type checker. 0 is
   silent, 1 prints a tree of the type derivation and 2 is like 1 but
   with much more debug information. *)
let opt_tc_debug = ref 0

(* opt_no_effects turns of the effect checking. This can break
   re-writer passes, so it should only be used for debugging. *)
let opt_no_effects = ref false

(* opt_no_lexp_bounds_check turns of the bounds checking in vector
   assignments in l-expressions *)
let opt_no_lexp_bounds_check = ref false

(* opt_expand_valspec expands typedefs in valspecs during type check.
   We prefer not to do it for latex output but it is otherwise a good idea. *)
let opt_expand_valspec = ref true

(* Linearize cases involving power where we would otherwise require
   the SMT solver to use non-linear arithmetic. *)
let opt_smt_linearize = ref false

(* Allow use of div and mod when rewriting nexps *)
let opt_smt_div = ref false

(* Use new bitfield syntax, more compatible with ASL *)
let opt_new_bitfields = ref false

(* Don't expand bitfields (when using old syntax), used for LaTeX output *)
let opt_no_bitfield_expansion = ref false

(* Check pattern-match completeness when type-checking *)
let opt_check_completeness = ref false
                              
let depth = ref 0

let rec indent n = match n with
  | 0 -> ""
  | n -> "|   " ^ indent (n - 1)

(* Lazily evaluate debugging message. This can make a big performance
   difference; for example, repeated calls to string_of_exp can be costly for
   deeply nested expressions, e.g. with long sequences of monadic binds. *)
let typ_debug ?level:(level=1) m = if !opt_tc_debug > level then prerr_endline (indent !depth ^ Lazy.force m) else ()

let typ_print m = if !opt_tc_debug > 0 then prerr_endline (indent !depth ^ Lazy.force m) else ()

type type_error =
  (* First parameter is the error that caused us to start doing type
     coercions, the second is the errors encountered by all possible
     coercions *)
  | Err_no_casts of unit exp * typ * typ * type_error * type_error list
  | Err_no_overloading of id * (id * type_error) list
  | Err_unresolved_quants of id * quant_item list * (mut * typ) Bindings.t * n_constraint list
  | Err_lexp_bounds of n_constraint * (mut * typ) Bindings.t * n_constraint list
  | Err_subtype of typ * typ * n_constraint list * Ast.l KBindings.t
  | Err_no_num_ident of id
  | Err_other of string
  | Err_because of type_error * Parse_ast.l * type_error

type env =
  { top_val_specs : (typquant * typ) Bindings.t;
    top_outcomes : (typquant * typ * kinded_id list) Bindings.t;
    defined_val_specs : IdSet.t;
    locals : (mut * typ) Bindings.t;
    top_letbinds : IdSet.t;
    union_ids : (typquant * typ) Bindings.t;
    registers : (effect * effect * typ) Bindings.t;
    variants : (typquant * type_union list) Bindings.t;
    scattered_variant_envs : env Bindings.t;
    mappings : (typquant * typ * typ) Bindings.t;
    typ_vars : (Ast.l * kind_aux) KBindings.t;
    shadow_vars : int KBindings.t;
    typ_synonyms : (typquant * typ_arg) Bindings.t;
    typ_params : typquant Bindings.t;
    overloads : (id list) Bindings.t;
    enums : IdSet.t Bindings.t;
    records : (typquant * (typ * id) list) Bindings.t;
    accessors : (typquant * typ) Bindings.t;
    externs : (string * string) list Bindings.t;
    casts : id list;
    allow_casts : bool;
    allow_bindings : bool;
    constraints : n_constraint list;
    default_order : order option;
    ret_typ : typ option;
    poly_undefineds : bool;
    prove : (env -> n_constraint -> bool) option;
    allow_unknowns : bool;
    bitfields : (Big_int.num * Big_int.num) Bindings.t Bindings.t;
    toplevel : l option;
    outcome_typschm : (typquant * typ) option;
  }

exception Type_error of env * l * type_error;;

let typ_error env l m = raise (Type_error (env, l, Err_other m))

let typ_raise env l err = raise (Type_error (env, l, err))

let deinfix = function
  | Id_aux (Id v, l) -> Id_aux (Operator v, l)
  | Id_aux (Operator v, l) -> Id_aux (Operator v, l)

let field_name rec_id id =
  match rec_id, id with
  | Id_aux (Id r, _), Id_aux (Id v, l) -> Id_aux (Id (r ^ "." ^ v), l)
  | _, _ -> assert false

let string_of_bind (typquant, typ) = string_of_typquant typquant ^ ". " ^ string_of_typ typ

let orig_kid (Kid_aux (Var v, l) as kid) =
  try
    let i = String.rindex v '#' in
    if i >= 3 && String.sub v 0 3 = "'fv" then
      Kid_aux (Var ("'" ^ String.sub v (i + 1) (String.length v - i - 1)), l)
    else kid
  with
  | Not_found -> kid

let is_list (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [A_aux (A_typ typ, _)])
       when string_of_id f = "list" -> Some typ
  | _ -> None

let is_unknown_type = function
  | (Typ_aux (Typ_internal_unknown, _)) -> true
  | _ -> false

let is_atom (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [_]) when string_of_id f = "atom" -> true
  | _ -> false

let is_atom_bool (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [_]) when string_of_id f = "atom_bool" -> true
  | _ -> false

let rec strip_id = function
  | Id_aux (Id x, _) -> Id_aux (Id x, Parse_ast.Unknown)
  | Id_aux (Operator x, _) -> Id_aux (Operator x, Parse_ast.Unknown)
and strip_kid = function
  | Kid_aux (Var x, _) -> Kid_aux (Var x, Parse_ast.Unknown)
and strip_base_effect = function
  | BE_aux (eff, _) -> BE_aux (eff, Parse_ast.Unknown)
and strip_effect = function
  | Effect_aux (Effect_set effects, _) -> Effect_aux (Effect_set (List.map strip_base_effect effects), Parse_ast.Unknown)
and strip_nexp_aux = function
  | Nexp_id id -> Nexp_id (strip_id id)
  | Nexp_var kid -> Nexp_var (strip_kid kid)
  | Nexp_constant n -> Nexp_constant n
  | Nexp_app (id, nexps) -> Nexp_app (id, List.map strip_nexp nexps)
  | Nexp_times (nexp1, nexp2) -> Nexp_times (strip_nexp nexp1, strip_nexp nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (strip_nexp nexp1, strip_nexp nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (strip_nexp nexp1, strip_nexp nexp2)
  | Nexp_exp nexp -> Nexp_exp (strip_nexp nexp)
  | Nexp_neg nexp -> Nexp_neg (strip_nexp nexp)
and strip_nexp = function
  | Nexp_aux (nexp_aux, _) -> Nexp_aux (strip_nexp_aux nexp_aux, Parse_ast.Unknown)
and strip_n_constraint_aux = function
  | NC_equal (nexp1, nexp2) -> NC_equal (strip_nexp nexp1, strip_nexp nexp2)
  | NC_bounded_ge (nexp1, nexp2) -> NC_bounded_ge (strip_nexp nexp1, strip_nexp nexp2)
  | NC_bounded_gt (nexp1, nexp2) -> NC_bounded_gt (strip_nexp nexp1, strip_nexp nexp2)
  | NC_bounded_le (nexp1, nexp2) -> NC_bounded_le (strip_nexp nexp1, strip_nexp nexp2)
  | NC_bounded_lt (nexp1, nexp2) -> NC_bounded_lt (strip_nexp nexp1, strip_nexp nexp2)
  | NC_not_equal (nexp1, nexp2) -> NC_not_equal (strip_nexp nexp1, strip_nexp nexp2)
  | NC_set (kid, nums) -> NC_set (strip_kid kid, nums)
  | NC_or (nc1, nc2) -> NC_or (strip_n_constraint nc1, strip_n_constraint nc2)
  | NC_and (nc1, nc2) -> NC_and (strip_n_constraint nc1, strip_n_constraint nc2)
  | NC_var kid -> NC_var (strip_kid kid)
  | NC_app (id, args) -> NC_app (strip_id id, List.map strip_typ_arg args)
  | NC_true -> NC_true
  | NC_false -> NC_false
and strip_n_constraint = function
  | NC_aux (nc_aux, _) -> NC_aux (strip_n_constraint_aux nc_aux, Parse_ast.Unknown)
and strip_typ_arg = function
  | A_aux (typ_arg_aux, _) -> A_aux (strip_typ_arg_aux typ_arg_aux, Parse_ast.Unknown)
and strip_typ_arg_aux = function
  | A_nexp nexp -> A_nexp (strip_nexp nexp)
  | A_typ typ -> A_typ (strip_typ typ)
  | A_order ord -> A_order (strip_order ord)
  | A_bool nc -> A_bool (strip_n_constraint nc)
and strip_order = function
  | Ord_aux (ord_aux, _) -> Ord_aux (strip_order_aux ord_aux, Parse_ast.Unknown)
and strip_order_aux = function
  | Ord_var kid -> Ord_var (strip_kid kid)
  | Ord_inc -> Ord_inc
  | Ord_dec -> Ord_dec
and strip_typ_aux : typ_aux -> typ_aux = function
  | Typ_internal_unknown -> Typ_internal_unknown
  | Typ_id id -> Typ_id (strip_id id)
  | Typ_var kid -> Typ_var (strip_kid kid)
  | Typ_fn (arg_typs, ret_typ, effect) -> Typ_fn (List.map strip_typ arg_typs, strip_typ ret_typ, strip_effect effect)
  | Typ_bidir (typ1, typ2, effect) -> Typ_bidir (strip_typ typ1, strip_typ typ2, strip_effect effect)
  | Typ_tup typs -> Typ_tup (List.map strip_typ typs)
  | Typ_exist (kopts, constr, typ) ->
     Typ_exist ((List.map strip_kinded_id kopts), strip_n_constraint constr, strip_typ typ)
  | Typ_app (id, args) -> Typ_app (strip_id id, List.map strip_typ_arg args)
and strip_typ : typ -> typ = function
  | Typ_aux (typ_aux, _) -> Typ_aux (strip_typ_aux typ_aux, Parse_ast.Unknown)
and strip_typq = function TypQ_aux (typq_aux, l) -> TypQ_aux (strip_typq_aux typq_aux, Parse_ast.Unknown)
and strip_typq_aux = function
  | TypQ_no_forall -> TypQ_no_forall
  | TypQ_tq quants -> TypQ_tq (List.map strip_quant_item quants)
and strip_quant_item = function
  | QI_aux (qi_aux, _) -> QI_aux (strip_qi_aux qi_aux, Parse_ast.Unknown)
and strip_qi_aux = function
  | QI_id kinded_id -> QI_id (strip_kinded_id kinded_id)
  | QI_constant kopts -> QI_constant (List.map strip_kinded_id kopts)
  | QI_constraint constr -> QI_constraint (strip_n_constraint constr)
and strip_kinded_id = function
  | KOpt_aux (kinded_id_aux, _) -> KOpt_aux (strip_kinded_id_aux kinded_id_aux, Parse_ast.Unknown)
and strip_kinded_id_aux = function
  | KOpt_kind (kind, kid) -> KOpt_kind (strip_kind kind, strip_kid kid)
and strip_kind = function
  | K_aux (k_aux, _) -> K_aux (k_aux, Parse_ast.Unknown)

let rec typ_constraints (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_internal_unknown -> []
  | Typ_id v -> []
  | Typ_var kid -> []
  | Typ_tup typs -> List.concat (List.map typ_constraints typs)
  | Typ_app (f, args) -> List.concat (List.map typ_arg_nexps args)
  | Typ_exist (kids, nc, typ) -> typ_constraints typ
  | Typ_fn (arg_typs, ret_typ, _) ->
     List.concat (List.map typ_constraints arg_typs) @ typ_constraints ret_typ
  | Typ_bidir (typ1, typ2, _) ->
     typ_constraints typ1 @ typ_constraints typ2
and typ_arg_nexps (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | A_nexp n -> []
  | A_typ typ -> typ_constraints typ
  | A_bool nc -> [nc]
  | A_order ord -> []

let rec typ_nexps (Typ_aux (typ_aux, l)) =
  match typ_aux with
  | Typ_internal_unknown -> []
  | Typ_id v -> []
  | Typ_var kid -> []
  | Typ_tup typs -> List.concat (List.map typ_nexps typs)
  | Typ_app (f, args) -> List.concat (List.map typ_arg_nexps args)
  | Typ_exist (kids, nc, typ) -> typ_nexps typ
  | Typ_fn (arg_typs, ret_typ, _) ->
     List.concat (List.map typ_nexps arg_typs) @ typ_nexps ret_typ
  | Typ_bidir (typ1, typ2, _) ->
     typ_nexps typ1 @ typ_nexps typ2
and typ_arg_nexps (A_aux (typ_arg_aux, l)) =
  match typ_arg_aux with
  | A_nexp n -> [n]
  | A_typ typ -> typ_nexps typ
  | A_bool nc -> constraint_nexps nc
  | A_order ord -> []
and constraint_nexps (NC_aux (nc_aux, l)) =
  match nc_aux with
  | NC_equal (n1, n2) | NC_bounded_ge (n1, n2) | NC_bounded_le (n1, n2) | NC_bounded_gt (n1, n2) | NC_bounded_lt (n1, n2) | NC_not_equal (n1, n2) ->
     [n1; n2]
  | NC_set _ | NC_true | NC_false | NC_var _ -> []
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) -> constraint_nexps nc1 @ constraint_nexps nc2
  | NC_app (_, args) -> List.concat (List.map typ_arg_nexps args)

(* Replace A_nexp nexp with A_nexp nexp' in typ, intended for use after typ_nexps. *)
let rec replace_nexp_typ nexp nexp' (Typ_aux (typ_aux, l) as typ) =
  let rep_typ = replace_nexp_typ nexp nexp' in
  match typ_aux with
  | Typ_internal_unknown
  | Typ_id _
  | Typ_var _
    -> typ
  | Typ_tup typs -> Typ_aux (Typ_tup (List.map rep_typ typs), l)
  | Typ_app (f, args) -> Typ_aux (Typ_app (f, List.map (replace_nexp_typ_arg nexp nexp') args), l)
  | Typ_exist (kids, nc, typ) -> Typ_aux (Typ_exist (kids, nc, rep_typ typ), l)
  | Typ_fn (arg_typs, ret_typ, eff) -> Typ_aux (Typ_fn (List.map rep_typ arg_typs, rep_typ ret_typ, eff), l)
  | Typ_bidir (typ1, typ2, eff) -> Typ_aux (Typ_bidir (rep_typ typ1, rep_typ typ2, eff), l)
and replace_nexp_typ_arg nexp nexp' (A_aux (typ_arg_aux, l) as arg) =
  match typ_arg_aux with
  | A_nexp n -> if Nexp.compare n nexp == 0 then (A_aux (A_nexp nexp', l)) else arg
  | A_typ typ -> A_aux (A_typ (replace_nexp_typ nexp nexp' typ), l)
  | A_bool nc -> A_aux (A_bool (replace_nexp_nc nexp nexp' nc), l)
  | A_order _ -> arg
and replace_nexp_nc nexp nexp' (NC_aux (nc_aux, l) as nc) =
  let rep_nc = replace_nexp_nc nexp nexp' in
  let rep n = if Nexp.compare n nexp == 0 then nexp' else n in
  match nc_aux with
  | NC_equal (n1, n2) -> NC_aux (NC_equal (rep n1, rep n2), l)
  | NC_bounded_ge (n1, n2) -> NC_aux (NC_bounded_ge (rep n1, rep n2), l)
  | NC_bounded_le (n1, n2) -> NC_aux (NC_bounded_le (rep n1, rep n2), l)
  | NC_bounded_gt (n1, n2) -> NC_aux (NC_bounded_gt (rep n1, rep n2), l)
  | NC_bounded_lt (n1, n2) -> NC_aux (NC_bounded_lt (rep n1, rep n2), l)
  | NC_not_equal (n1, n2) -> NC_aux (NC_not_equal (rep n1, rep n2), l)
  | NC_set _ | NC_true | NC_false | NC_var _ -> nc
  | NC_or (nc1, nc2) -> NC_aux (NC_or (rep_nc nc1, rep_nc nc2), l)
  | NC_and (nc1, nc2) -> NC_aux (NC_and (rep_nc nc1, rep_nc nc2), l)
  | NC_app (f, args) -> NC_aux (NC_app (f, List.map (replace_nexp_typ_arg nexp nexp') args), l)

(* Similarly for constraints *)
let rec replace_nc_typ nc nc' (Typ_aux (typ_aux, l) as typ) =
  let rep_typ = replace_nc_typ nc nc' in
  match typ_aux with
  | Typ_internal_unknown
  | Typ_id _
  | Typ_var _
    -> typ
  | Typ_tup typs -> Typ_aux (Typ_tup (List.map rep_typ typs), l)
  | Typ_app (f, args) -> Typ_aux (Typ_app (f, List.map (replace_nc_typ_arg nc nc') args), l)
  | Typ_exist (kids, nc, typ) -> Typ_aux (Typ_exist (kids, nc, rep_typ typ), l)
  | Typ_fn (arg_typs, ret_typ, eff) -> Typ_aux (Typ_fn (List.map rep_typ arg_typs, rep_typ ret_typ, eff), l)
  | Typ_bidir (typ1, typ2, eff) -> Typ_aux (Typ_bidir (rep_typ typ1, rep_typ typ2, eff), l)
and replace_nc_typ_arg nc nc' (A_aux (typ_arg_aux, l) as arg) =
  match typ_arg_aux with
  | A_nexp _ -> arg
  | A_typ typ -> A_aux (A_typ (replace_nc_typ nc nc' typ), l)
  | A_bool nc'' -> if NC.compare nc nc'' == 0 then A_aux (A_bool nc', l) else arg
  | A_order _ -> arg

(* Return a KidSet containing all the type variables appearing in
   nexp, where nexp occurs underneath a Nexp_exp, i.e. 2^nexp *)
let rec nexp_power_variables (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) ->
     KidSet.union (nexp_power_variables n1) (nexp_power_variables n2)
  | Nexp_neg n ->
     nexp_power_variables n
  | Nexp_id _ | Nexp_var _ | Nexp_constant _ ->
     KidSet.empty
  | Nexp_app (_, ns) ->
     List.fold_left KidSet.union KidSet.empty (List.map nexp_power_variables ns)
  | Nexp_exp n ->
     tyvars_of_nexp n

let constraint_power_variables nc =
  List.fold_left KidSet.union KidSet.empty (List.map nexp_power_variables (constraint_nexps nc))

let rec name_pat (P_aux (aux, _)) =
  match aux with
  | P_id id | P_as (_, id) -> Some ("_" ^ string_of_id id)
  | P_typ (_, pat) | P_var (pat, _) -> name_pat pat
  | _ -> None

let ex_counter = ref 0

let fresh_existential k =
  let fresh = Kid_aux (Var ("'ex" ^ string_of_int !ex_counter ^ "#"), Parse_ast.Unknown) in
  incr ex_counter; mk_kopt k fresh

let named_existential k = function
  | Some n -> mk_kopt k (mk_kid n)
  | None -> fresh_existential k

let destruct_exist_plain ?name:(name=None) typ =
  match typ with
  | Typ_aux (Typ_exist ([kopt], nc, typ), _) ->
     let kid, fresh = kopt_kid kopt, named_existential (unaux_kind (kopt_kind kopt)) name in
     let nc = constraint_subst kid (arg_kopt fresh) nc in
     let typ = typ_subst kid (arg_kopt fresh) typ in
     Some ([fresh], nc, typ)
  | Typ_aux (Typ_exist (kopts, nc, typ), _) ->
     let add_num i = match name with Some n -> Some (n ^ string_of_int i) | None -> None in 
     let fresh_kopts =
       List.mapi (fun i kopt -> (kopt_kid kopt, named_existential (unaux_kind (kopt_kind kopt)) (add_num i))) kopts
     in
     let nc = List.fold_left (fun nc (kid, fresh) -> constraint_subst kid (arg_kopt fresh) nc) nc fresh_kopts in
     let typ = List.fold_left (fun typ (kid, fresh) -> typ_subst kid (arg_kopt fresh) typ) typ fresh_kopts in
     Some (List.map snd fresh_kopts, nc, typ)
  | _ -> None

(** Destructure and canonicalise a numeric type into a list of type
   variables, a constraint on those type variables, and an
   N-expression that represents that numeric type in the
   environment. For example:
   - {'n, 'n <= 10. atom('n)} => ['n], 'n <= 10, 'n
   - int => ['n], true, 'n (where x is fresh)
   - atom('n) => [], true, 'n
**)
let destruct_numeric ?name:(name=None) typ =
  match destruct_exist_plain ~name:name typ, typ with
  | Some (kids, nc, Typ_aux (Typ_app (id, [A_aux (A_nexp nexp, _)]), _)), _ when string_of_id id = "atom" ->
     Some (List.map kopt_kid kids, nc, nexp)
  | None, Typ_aux (Typ_app (id, [A_aux (A_nexp nexp, _)]), _) when string_of_id id = "atom" ->
     Some ([], nc_true, nexp)
  | None, Typ_aux (Typ_app (id, [A_aux (A_nexp lo, _); A_aux (A_nexp hi, _)]), _) when string_of_id id = "range" ->
     let kid = kopt_kid (named_existential K_int name) in
     Some ([kid], nc_and (nc_lteq lo (nvar kid)) (nc_lteq (nvar kid) hi), nvar kid)
  | None, Typ_aux (Typ_id id, _) when string_of_id id = "nat" ->
     let kid = kopt_kid (named_existential K_int name) in
     Some ([kid], nc_lteq (nint 0) (nvar kid), nvar kid)
  | None, Typ_aux (Typ_id id, _) when string_of_id id = "int" ->
     let kid = kopt_kid (named_existential K_int name) in
     Some ([kid], nc_true, nvar kid)
  | _, _ -> None

let destruct_boolean ?name:(name=None) = function
  | Typ_aux (Typ_id (Id_aux (Id "bool", _)), _) ->
     let kid = kopt_kid (fresh_existential K_bool) in
     Some (kid, nc_var kid)
  | _ -> None

let destruct_exist ?name:(name=None) typ =
  match destruct_numeric ~name:name typ with
  | Some (kids, nc, nexp) -> Some (List.map (mk_kopt K_int) kids, nc, atom_typ nexp)
  | None ->
     match destruct_boolean ~name:name typ with
     | Some (kid, nc) -> Some ([mk_kopt K_bool kid], nc_true, atom_bool_typ nc)
     | None -> destruct_exist_plain ~name:name typ

let adding = Util.("Adding " |> darkgray |> clear)

(**************************************************************************)
(* 1. Environment                                                         *)
(**************************************************************************)

module Env : sig
  type t = env
  val add_val_spec : id -> typquant * typ -> t -> t
  val add_outcome : id -> typquant * typ * kinded_id list -> t -> t
  val update_val_spec : id -> typquant * typ -> t -> t
  val define_val_spec : id -> t -> t
  val get_defined_val_specs : t -> IdSet.t
  val get_val_spec : id -> t -> typquant * typ
  val get_val_specs : t -> (typquant * typ ) Bindings.t
  val get_val_spec_orig : id -> t -> typquant * typ
  val get_outcome : l -> id -> env -> typquant * typ * kinded_id list
  val is_union_constructor : id -> t -> bool
  val is_singleton_union_constructor : id -> t -> bool
  val is_mapping : id -> t -> bool
  val add_record : id -> typquant -> (typ * id) list -> t -> t
  val is_record : id -> t -> bool
  val get_record : id -> t -> typquant * (typ * id) list
  val get_records : t -> (typquant * (typ * id) list) Bindings.t
  val get_accessor_fn : id -> id -> t -> typquant * typ
  val get_accessor : id -> id -> t -> typquant * typ * typ * effect
  val add_local : id -> mut * typ -> t -> t
  val get_locals : t -> (mut * typ) Bindings.t
  val add_toplevel_lets : IdSet.t -> t -> t
  val get_toplevel_lets : t -> IdSet.t
  val add_variant : id -> typquant * type_union list -> t -> t
  val add_scattered_variant : id -> typquant -> t -> t
  val add_variant_clause : id -> type_union -> t -> t
  val get_variant : id -> t -> typquant * type_union list
  val get_variants : t -> (typquant * type_union list) Bindings.t
  val get_scattered_variant_env : id -> t -> t
  val add_mapping : id -> typquant * typ * typ * effect -> t -> t
  val add_union_id : id -> typquant * typ -> t -> t
  val get_union_id  : id -> t -> typquant * typ
  val is_register : id -> t -> bool
  val get_register : id -> t -> effect * effect * typ
  val get_registers : t -> (effect * effect * typ) Bindings.t
  val add_register : id -> effect -> effect -> typ -> t -> t
  val is_mutable : id -> t -> bool
  val get_constraints : t -> n_constraint list
  val add_constraint : n_constraint -> t -> t
  val add_typquant : l -> typquant -> t -> t
  val get_typ_var : kid -> t -> kind_aux
  val get_typ_var_loc : kid -> t -> Ast.l
  val get_typ_var_loc_opt : kid -> t -> Ast.l option
  val get_typ_vars : t -> kind_aux KBindings.t
  val get_typ_var_locs : t -> Ast.l KBindings.t
  val shadows : kid -> t -> int
  val add_typ_var_shadow : l -> kinded_id -> t -> t * kid option
  val add_typ_var : l -> kinded_id -> t -> t
  val get_ret_typ : t -> typ option
  val add_ret_typ : typ -> t -> t
  val add_typ_synonym : id -> typquant -> typ_arg -> t -> t
  val get_typ_synonym : id -> t -> Ast.l -> t -> typ_arg list -> typ_arg
  val get_typ_synonyms : t -> (typquant * typ_arg) Bindings.t
  val add_overloads : id -> id list -> t -> t
  val get_overloads : id -> t -> id list
  val is_extern : id -> t -> string -> bool
  val add_extern : id -> (string * string) list -> t -> t
  val get_extern : id -> t -> string -> string
  val get_default_order : t -> order
  val get_default_order_option : t -> order option
  val set_default_order : order -> t -> t
  val add_enum : id -> id list -> t -> t
  val get_enum : id -> t -> id list
  val get_enums : t -> IdSet.t Bindings.t 
  val is_enum : id -> t -> bool
  val get_casts : t -> id list
  val allow_casts : t -> bool
  val no_casts : t -> t
  val enable_casts : t -> t
  val add_cast : id -> t -> t
  val allow_polymorphic_undefineds : t -> t
  val polymorphic_undefineds : t -> bool
  val lookup_id : ?raw:bool -> id -> t -> typ lvar
  val fresh_kid : ?kid:kid -> t -> kid
  val expand_synonyms : t -> typ -> typ
  val expand_nexp_synonyms : t -> nexp -> nexp
  val expand_constraint_synonyms : t -> n_constraint -> n_constraint
  val base_typ_of : t -> typ -> typ
  val allow_unknowns : t -> bool
  val set_allow_unknowns : bool -> t -> t
  val add_bitfield : id -> (Big_int.num * Big_int.num) Bindings.t -> t -> t
  val get_bitfield_range : l -> id -> id -> t -> (Big_int.num * Big_int.num)

  val no_bindings : t -> t

  (* Well formedness-checks *)
  val wf_typ : t -> typ -> unit
  val wf_nexp : ?exs:KidSet.t -> t -> nexp -> unit
  val wf_constraint : ?exs:KidSet.t -> t -> n_constraint -> unit

  (* Some of the code in the environment needs to use the smt solver,
     which is defined below. To break the circularity this would cause
     (as the prove code depends on the environment), we add a
     reference to the prover to the initial environment. *)
  val set_prover : (t -> n_constraint -> bool) option -> t -> t

  (* This must not be exported, initial_env sets up a correct initial
     environment. *)
  val empty : t

  val builtin_typs : typquant Bindings.t
end = struct
  type t = env

  let empty =
    { top_val_specs = Bindings.empty;
      top_outcomes = Bindings.empty;
      defined_val_specs = IdSet.empty;
      locals = Bindings.empty;
      top_letbinds = IdSet.empty;
      union_ids = Bindings.empty;
      registers = Bindings.empty;
      variants = Bindings.empty;
      scattered_variant_envs = Bindings.empty;
      mappings = Bindings.empty;
      typ_vars = KBindings.empty;
      shadow_vars = KBindings.empty;
      typ_synonyms = Bindings.empty;
      typ_params = Bindings.empty;
      overloads = Bindings.empty;
      enums = Bindings.empty;
      records = Bindings.empty;
      accessors = Bindings.empty;
      externs = Bindings.empty;
      casts = [];
      allow_bindings = true;
      allow_casts = true;
      constraints = [];
      default_order = None;
      ret_typ = None;
      poly_undefineds = false;
      prove = None;
      allow_unknowns = false;
      bitfields = Bindings.empty;
      toplevel = None;
      outcome_typschm = None;
    }

  let set_prover f env = { env with prove = f }

  let allow_unknowns env = env.allow_unknowns
  let set_allow_unknowns b env = { env with allow_unknowns = b }

  (* First, we define how type variables are added to the
     environment. If we add a new variable shadowing a previous
     variable, we need to modify the environment so the shadowed
     variable is renamed. We can't just remove it because it may be
     referenced by constraints. *)
  let shadows v env = match KBindings.find_opt v env.shadow_vars with Some n -> n | None -> 0
 
  let add_typ_var_shadow l (KOpt_aux (KOpt_kind (K_aux (k, _), v), _)) env =
    if KBindings.mem v env.typ_vars then begin
        let n = match KBindings.find_opt v env.shadow_vars with Some n -> n | None -> 0 in
        let s_l, s_k = KBindings.find v env.typ_vars in
        let s_v = Kid_aux (Var (string_of_kid v ^ "#" ^ string_of_int n), l) in
        typ_print (lazy (Printf.sprintf "%stype variable (shadowing %s) %s : %s" adding (string_of_kid s_v) (string_of_kid v) (string_of_kind_aux k)));
        { env with
          constraints = List.map (constraint_subst v (arg_kopt (mk_kopt s_k s_v))) env.constraints;
          typ_vars = KBindings.add v (l, k) (KBindings.add s_v (s_l, s_k) env.typ_vars);
          locals = Bindings.map (fun (mut, typ) -> mut, typ_subst v (arg_kopt (mk_kopt s_k s_v)) typ) env.locals;
          shadow_vars = KBindings.add v (n + 1) env.shadow_vars
        }, Some s_v
      end
    else begin
        typ_print (lazy (adding ^ "type variable " ^ string_of_kid v ^ " : " ^ string_of_kind_aux k));
        { env with typ_vars = KBindings.add v (l, k) env.typ_vars }, None
      end

  let add_typ_var l kopt env = fst (add_typ_var_shadow l kopt env)
                               
  let get_typ_var_loc_opt kid env =
    match KBindings.find_opt kid env.typ_vars with
    | Some (l, _) -> Some l
    | None -> None
                               
  let get_typ_var kid env =
    try snd (KBindings.find kid env.typ_vars) with
    | Not_found -> typ_error env (kid_loc kid) ("No type variable " ^ string_of_kid kid)

  let get_typ_var_loc kid env =
    try fst (KBindings.find kid env.typ_vars) with
    | Not_found -> typ_error env (kid_loc kid) ("No type variable " ^ string_of_kid kid)

  let get_typ_vars env = KBindings.map snd env.typ_vars
  let get_typ_var_locs env = KBindings.map fst env.typ_vars

  let k_counter = ref 0
  let k_name () = let kid = mk_kid ("k#" ^ string_of_int !k_counter) in incr k_counter; kid

  let kinds_typq kinds = mk_typquant (List.map (fun k -> mk_qi_id k (k_name ())) kinds)

  let builtin_typs =
    List.fold_left (fun m (name, kinds) -> Bindings.add (mk_id name) (kinds_typq kinds) m) Bindings.empty
      [ ("range", [K_int; K_int]);
        ("atom", [K_int]);
        ("implicit", [K_int]);
        ("vector", [K_int; K_order; K_type]);
        ("bitvector", [K_int; K_order]);
        ("register", [K_type]);
        ("bit", []);
        ("unit", []);
        ("int", []);
        ("nat", []);
        ("bool", []);
        ("real", []);
        ("list", [K_type]);
        ("string", []);
        ("itself", [K_int]);
        ("atom_bool", [K_bool])
      ]

  let builtin_mappings =
    List.fold_left (fun m (name, typ) -> Bindings.add (mk_id name) typ m) Bindings.empty
      [
        ("int", Typ_bidir(int_typ, string_typ, no_effect));
        ("nat", Typ_bidir(nat_typ, string_typ, no_effect));
      ]
 
  let bound_typ_id env id =
    Bindings.mem id env.typ_synonyms
    || Bindings.mem id env.variants
    || Bindings.mem id env.records
    || Bindings.mem id env.enums
    || Bindings.mem id builtin_typs

  let bound_ctor_fn env id =
    Bindings.mem id env.top_val_specs
    || Bindings.mem id env.union_ids
    
  let get_overloads id env =
    try Bindings.find id env.overloads with
    | Not_found -> []

  let add_overloads id ids env =
    typ_print (lazy (adding ^ "overloads for " ^ string_of_id id ^ " [" ^ string_of_list ", " string_of_id ids ^ "]"));
    let existing = try Bindings.find id env.overloads with Not_found -> [] in
    { env with overloads = Bindings.add id (existing @ ids) env.overloads }

  let rec infer_kind env id =
    if Bindings.mem id builtin_typs then
      Bindings.find id builtin_typs
    else if Bindings.mem id env.variants then
      fst (Bindings.find id env.variants)
    else if Bindings.mem id env.records then
      fst (Bindings.find id env.records)
    else if Bindings.mem id env.enums then
      mk_typquant []
    else if Bindings.mem id env.typ_synonyms then
      typ_error env (id_loc id) ("Cannot infer kind of type synonym " ^ string_of_id id)
    else
      typ_error env (id_loc id) ("Cannot infer kind of " ^  string_of_id id)

  let check_args_typquant id env args typq =
    let kopts, ncs = quant_split typq in
    let rec subst_args kopts args =
      match kopts, args with
      | kopt :: kopts, (A_aux (A_nexp _, _) as arg) :: args when is_int_kopt kopt ->
         List.map (constraint_subst (kopt_kid kopt) arg) (subst_args kopts args)
      | kopt :: kopts, A_aux (A_typ arg, _) :: args when is_typ_kopt kopt ->
         subst_args kopts args
      | kopt :: kopts, A_aux (A_order arg, _) :: args when is_order_kopt kopt ->
         subst_args kopts args
      | kopt :: kopts, A_aux (A_bool arg, _) :: args when is_bool_kopt kopt ->
         subst_args kopts args
      | [], [] -> ncs
      | _, A_aux (_, l) :: _ -> typ_error env l ("Error when processing type quantifer arguments " ^ string_of_typquant typq)
      | _, _ -> typ_error env Parse_ast.Unknown ("Error when processing type quantifer arguments " ^ string_of_typquant typq)
    in
    let ncs = subst_args kopts args in
    if (match env.prove with Some prover -> List.for_all (prover env) ncs | None -> false)
    then ()
    else typ_error env (id_loc id) ("Could not prove " ^ string_of_list ", " string_of_n_constraint ncs ^ " for type constructor " ^ string_of_id id)

  let mk_synonym typq typ_arg =
    let kopts, ncs = quant_split typq in
    let kopts = List.map (fun kopt -> kopt, fresh_existential (unaux_kind (kopt_kind kopt))) kopts in
    let ncs = List.map (fun nc -> List.fold_left (fun nc (kopt, fresh) -> constraint_subst (kopt_kid kopt) (arg_kopt fresh) nc) nc kopts) ncs in
    let typ_arg = List.fold_left (fun typ_arg (kopt, fresh) -> typ_arg_subst (kopt_kid kopt) (arg_kopt fresh) typ_arg) typ_arg kopts in
    let kopts = List.map snd kopts in
    let rec subst_args env l kopts args =
      match kopts, args with
      | kopt :: kopts, A_aux (A_nexp arg, _) :: args when is_int_kopt kopt ->
         let typ_arg, ncs = subst_args env l kopts args in
         typ_arg_subst (kopt_kid kopt) (arg_nexp arg) typ_arg,
         List.map (constraint_subst (kopt_kid kopt) (arg_nexp arg)) ncs
      | kopt :: kopts, A_aux (A_typ arg, _) :: args when is_typ_kopt kopt ->
         let typ_arg, ncs = subst_args env l kopts args in
         typ_arg_subst (kopt_kid kopt) (arg_typ arg) typ_arg, ncs
      | kopt :: kopts, A_aux (A_order arg, _) :: args when is_order_kopt kopt ->
         let typ_arg, ncs = subst_args env l kopts args in
         typ_arg_subst (kopt_kid kopt) (arg_order arg) typ_arg, ncs
      | kopt :: kopts, A_aux (A_bool arg, _) :: args when is_bool_kopt kopt ->
         let typ_arg, ncs = subst_args env l kopts args in
         typ_arg_subst (kopt_kid kopt) (arg_bool arg) typ_arg, ncs
      | [], [] -> typ_arg, ncs
      | _, _ -> typ_error env l "Synonym applied to bad arguments"
    in
    fun l env args ->
    let typ_arg, ncs = subst_args env l kopts args in
    if (match env.prove with Some prover -> List.for_all (prover env) ncs | None -> false)
    then typ_arg
    else typ_error env l ("Could not prove constraints " ^ string_of_list ", " string_of_n_constraint ncs
                          ^ " in type synonym " ^ string_of_typ_arg typ_arg
                          ^ " with " ^ Util.string_of_list ", " string_of_n_constraint env.constraints)

  let get_typ_synonym id env =
    match Bindings.find_opt id env.typ_synonyms with
    | Some (typq, arg) -> mk_synonym typq arg
    | None -> raise Not_found

  let get_typ_synonyms env = env.typ_synonyms

  let get_constraints env = env.constraints
                           
  (** Map over all nexps in a type - excluding those in existential constraints **)
  let rec map_nexps f (Typ_aux (typ_aux, l) as typ) =
    match typ_aux with
    | Typ_internal_unknown
    | Typ_id _ | Typ_var _ -> typ
    | Typ_fn (arg_typs, ret_typ, effect) -> Typ_aux (Typ_fn (List.map (map_nexps f) arg_typs, map_nexps f ret_typ, effect), l)
    | Typ_bidir (typ1, typ2, effect) -> Typ_aux (Typ_bidir (map_nexps f typ1, map_nexps f typ2, effect), l)
    | Typ_tup typs -> Typ_aux (Typ_tup (List.map (map_nexps f) typs), l)
    | Typ_exist (kids, nc, typ) -> Typ_aux (Typ_exist (kids, nc, map_nexps f typ), l)
    | Typ_app (id, args) -> Typ_aux (Typ_app (id, List.map (map_nexps_arg f) args), l)
  and map_nexps_arg f (A_aux (arg_aux, l) as arg) =
    match arg_aux with
    | A_order _ | A_typ _ | A_bool _ -> arg
    | A_nexp n -> A_aux (A_nexp (f n), l)

  let wf_debug str f x exs =
    typ_debug ~level:2 (lazy ("wf_" ^ str ^ ": " ^ f x ^ " exs: " ^ Util.string_of_list ", " string_of_kid (KidSet.elements exs)))

  (* Check if a type, order, n-expression or constraint is
     well-formed. Throws a type error if the type is badly formed. *)
  let rec wf_typ' ?exs:(exs=KidSet.empty) env (Typ_aux (typ_aux, l) as typ) =
    match typ_aux with
    | Typ_id id when bound_typ_id env id ->
       let typq = infer_kind env id in
       if quant_kopts typq != []
       then typ_error env l ("Type constructor " ^ string_of_id id ^ " expected " ^ string_of_typquant typq)
       else ()
    | Typ_id id -> typ_error env l ("Undefined type " ^ string_of_id id)
    | Typ_var kid -> begin
      match KBindings.find kid env.typ_vars with
      | (_, K_type) -> ()
      | (_, k) -> typ_error env l ("Type variable " ^ string_of_kid kid ^ " in type " ^ string_of_typ typ
                               ^ " is " ^ string_of_kind_aux k ^ " rather than Type")
      | exception Not_found ->
         typ_error env l ("Unbound type variable " ^ string_of_kid kid ^ " in type " ^ string_of_typ typ)
    end
    | Typ_fn (arg_typs, ret_typ, effs) -> List.iter (wf_typ' ~exs:exs env) arg_typs; wf_typ' ~exs:exs env ret_typ
    | Typ_bidir (typ1, typ2, _) when strip_typ typ1 = strip_typ typ2 ->
       typ_error env l "Bidirectional types cannot be the same on both sides"
    | Typ_bidir (typ1, typ2, _) -> wf_typ' ~exs:exs env typ1; wf_typ' ~exs:exs env typ2
    | Typ_tup typs -> List.iter (wf_typ' ~exs:exs env) typs
    | Typ_app (id, [A_aux (A_nexp _, _) as arg]) when string_of_id id = "implicit" ->
       wf_typ_arg ~exs:exs env arg
    | Typ_app (id, args) when bound_typ_id env id ->
       List.iter (wf_typ_arg ~exs:exs env) args;
       check_args_typquant id env args (infer_kind env id)
    | Typ_app (id, _) -> typ_error env l ("Undefined type " ^ string_of_id id)
    | Typ_exist ([], _, _) -> typ_error env l ("Existential must have some type variables")
    | Typ_exist (kopts, nc, typ) when KidSet.is_empty exs ->
       wf_constraint ~exs:(KidSet.of_list (List.map kopt_kid kopts)) env nc;
       wf_typ' ~exs:(KidSet.of_list (List.map kopt_kid kopts)) env typ
    | Typ_exist (_, _, _) -> typ_error env l ("Nested existentials are not allowed")
    | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
  and wf_typ_arg ?exs:(exs=KidSet.empty) env (A_aux (typ_arg_aux, _)) =
    match typ_arg_aux with
    | A_nexp nexp -> wf_nexp ~exs:exs env nexp
    | A_typ typ -> wf_typ' ~exs:exs env typ
    | A_order ord -> wf_order env ord
    | A_bool nc -> wf_constraint ~exs:exs env nc
  and wf_nexp ?exs:(exs=KidSet.empty) env (Nexp_aux (nexp_aux, l) as nexp) =
    wf_debug "nexp" string_of_nexp nexp exs;
    match nexp_aux with
    | Nexp_id id -> typ_error env l ("Undefined type synonym " ^ string_of_id id)
    | Nexp_var kid when KidSet.mem kid exs -> ()
    | Nexp_var kid ->
       begin match get_typ_var kid env with
       | K_int -> ()
       | kind -> typ_error env l ("Constraint is badly formed, "
                              ^ string_of_kid kid ^ " has kind "
                              ^ string_of_kind_aux kind ^ " but should have kind Int")
       end
    | Nexp_constant _ -> ()
    | Nexp_app (id, nexps) ->
       List.iter (fun n -> wf_nexp ~exs:exs env n) nexps
    | Nexp_times (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_sum (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_minus (nexp1, nexp2) -> wf_nexp ~exs:exs env nexp1; wf_nexp ~exs:exs env nexp2
    | Nexp_exp nexp -> wf_nexp ~exs:exs env nexp (* MAYBE: Could put restrictions on what is allowed here *)
    | Nexp_neg nexp -> wf_nexp ~exs:exs env nexp
  and wf_order env (Ord_aux (ord_aux, l) as ord) =
    match ord_aux with
    | Ord_var kid ->
       begin match get_typ_var kid env with
       | K_order -> ()
       | kind -> typ_error env l ("Order is badly formed, "
                              ^ string_of_kid kid ^ " has kind "
                              ^ string_of_kind_aux kind ^ " but should have kind Order")
       end
    | Ord_inc | Ord_dec -> ()
  and wf_constraint ?exs:(exs=KidSet.empty) env (NC_aux (nc_aux, l) as nc) =
    wf_debug "constraint" string_of_n_constraint nc exs;
    match nc_aux with
    | NC_equal (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_not_equal (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_bounded_ge (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_bounded_gt (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_bounded_le (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_bounded_lt (n1, n2) -> wf_nexp ~exs:exs env n1; wf_nexp ~exs:exs env n2
    | NC_set (kid, _) when KidSet.mem kid exs -> ()
    | NC_set (kid, _) ->
       begin match get_typ_var kid env with
       | K_int -> ()
       | kind -> typ_error env l ("Set constraint is badly formed, "
                              ^ string_of_kid kid ^ " has kind "
                              ^ string_of_kind_aux kind ^ " but should have kind Int")
       end
    | NC_or (nc1, nc2) -> wf_constraint ~exs:exs env nc1; wf_constraint ~exs:exs env nc2
    | NC_and (nc1, nc2) -> wf_constraint ~exs:exs env nc1; wf_constraint ~exs:exs env nc2
    | NC_app (id, args) -> List.iter (wf_typ_arg ~exs:exs env) args
    | NC_var kid when KidSet.mem kid exs -> ()
    | NC_var kid ->
       begin match get_typ_var kid env with
       | K_bool -> ()
       | kind -> typ_error env l (string_of_kid kid ^ " has kind "
                              ^ string_of_kind_aux kind ^ " but should have kind Bool")
       end
    | NC_true | NC_false -> ()
 
  let rec expand_constraint_synonyms env (NC_aux (aux, l) as nc) =
    match aux with
    | NC_or (nc1, nc2) -> NC_aux (NC_or (expand_constraint_synonyms env nc1, expand_constraint_synonyms env nc2), l)
    | NC_and (nc1, nc2) -> NC_aux (NC_and (expand_constraint_synonyms env nc1, expand_constraint_synonyms env nc2), l)
    | NC_equal (n1, n2) -> NC_aux (NC_equal (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_not_equal (n1, n2) -> NC_aux (NC_not_equal (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_bounded_le (n1, n2) -> NC_aux (NC_bounded_le (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_bounded_lt (n1, n2) -> NC_aux (NC_bounded_lt (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_bounded_ge (n1, n2) -> NC_aux (NC_bounded_ge (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_bounded_gt (n1, n2) -> NC_aux (NC_bounded_gt (expand_nexp_synonyms env n1, expand_nexp_synonyms env n2), l)
    | NC_app (id, args) ->
       (try
          begin match get_typ_synonym id env l env args with
          | A_aux (A_bool nc, _) -> expand_constraint_synonyms env nc
          | arg -> typ_error env l ("Expected Bool when expanding synonym " ^ string_of_id id ^ " got " ^ string_of_typ_arg arg)
          end
        with Not_found -> NC_aux (NC_app (id, List.map (expand_arg_synonyms env) args), l))
    | NC_true | NC_false | NC_var _ | NC_set _ -> nc

  and expand_nexp_synonyms env (Nexp_aux (aux, l) as nexp) =
    match aux with
    | Nexp_app (id, args) ->
       (try
          begin match get_typ_synonym id env l env [] with
          | A_aux (A_nexp nexp, _) -> expand_nexp_synonyms env nexp
          | _ -> typ_error env l ("Expected Int when expanding synonym " ^ string_of_id id)
          end
        with
        | Not_found -> Nexp_aux (Nexp_app (id, List.map (expand_nexp_synonyms env) args), l))
    | Nexp_id id ->
       (try
          begin match get_typ_synonym id env l env [] with
          | A_aux (A_nexp nexp, _) -> expand_nexp_synonyms env nexp
          | _ -> typ_error env l ("Expected Int when expanding synonym " ^ string_of_id id)
          end
        with Not_found -> nexp)
    | Nexp_times (nexp1, nexp2) -> Nexp_aux (Nexp_times (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
    | Nexp_sum (nexp1, nexp2) -> Nexp_aux (Nexp_sum (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
    | Nexp_minus (nexp1, nexp2) -> Nexp_aux (Nexp_minus (expand_nexp_synonyms env nexp1, expand_nexp_synonyms env nexp2), l)
    | Nexp_exp nexp -> Nexp_aux (Nexp_exp (expand_nexp_synonyms env nexp), l)
    | Nexp_neg nexp -> Nexp_aux (Nexp_neg (expand_nexp_synonyms env nexp), l)
    | Nexp_var kid -> Nexp_aux (Nexp_var kid, l)
    | Nexp_constant n -> Nexp_aux (Nexp_constant n, l)

  and expand_synonyms env (Typ_aux (typ, l) as t) =
    match typ with
    | Typ_internal_unknown -> Typ_aux (Typ_internal_unknown, l)
    | Typ_tup typs -> Typ_aux (Typ_tup (List.map (expand_synonyms env) typs), l)
    | Typ_fn (arg_typs, ret_typ, effs) -> Typ_aux (Typ_fn (List.map (expand_synonyms env) arg_typs, expand_synonyms env ret_typ, effs), l)
    | Typ_bidir (typ1, typ2, effs) -> Typ_aux (Typ_bidir (expand_synonyms env typ1, expand_synonyms env typ2, effs), l)
    | Typ_app (id, args) ->
       (try
          begin match get_typ_synonym id env l env args with
          | A_aux (A_typ typ, _) -> expand_synonyms env typ
          | _ -> typ_error env l ("Expected Type when expanding synonym " ^ string_of_id id)
          end
        with
        | Not_found -> Typ_aux (Typ_app (id, List.map (expand_arg_synonyms env) args), l))
    | Typ_id id ->
       (try
          begin match get_typ_synonym id env l env [] with
          | A_aux (A_typ typ, _) -> expand_synonyms env typ
          | _ -> typ_error env l ("Expected Type when expanding synonym " ^ string_of_id id)
          end
        with
        | Not_found -> Typ_aux (Typ_id id, l))
    | Typ_exist (kopts, nc, typ) ->
       let nc = expand_constraint_synonyms env nc in
       
       (* When expanding an existential synonym we need to take care
          to add the type variables and constraints to the
          environment, so we can check constraints attached to type
          synonyms within the existential. Furthermore, we must take
          care to avoid clobbering any existing type variables in
          scope while doing this. *)
       let rebindings = ref [] in

       let rename_kopt (KOpt_aux (KOpt_kind (k, kid), l) as kopt) =
         if KBindings.mem kid env.typ_vars then
           KOpt_aux (KOpt_kind (k, prepend_kid "syn#" kid), l)
         else kopt
       in
       let add_typ_var env (KOpt_aux (KOpt_kind (k, kid), l) as kopt) =
         try
           let (l, _) = KBindings.find kid env.typ_vars in
           rebindings := kid :: !rebindings;
           { env with typ_vars = KBindings.add (prepend_kid "syn#" kid) (l, unaux_kind k) env.typ_vars }
         with
         | Not_found ->
            { env with typ_vars = KBindings.add kid (l, unaux_kind k) env.typ_vars }
       in

       let env = List.fold_left add_typ_var env kopts in
       let kopts = List.map rename_kopt kopts in
       let nc = List.fold_left (fun nc kid -> constraint_subst kid (arg_nexp (nvar (prepend_kid "syn#" kid))) nc) nc !rebindings in
       let typ = List.fold_left (fun typ kid -> typ_subst kid (arg_nexp (nvar (prepend_kid "syn#" kid))) typ) typ !rebindings in
       let env = add_constraint nc env in
       Typ_aux (Typ_exist (kopts, nc, expand_synonyms env typ), l)
    | Typ_var v -> Typ_aux (Typ_var v, l)

  and expand_arg_synonyms env (A_aux (typ_arg, l)) =
    match typ_arg with
    | A_typ typ -> A_aux (A_typ (expand_synonyms env typ), l)
    | A_bool nc -> A_aux (A_bool (expand_constraint_synonyms env nc), l)
    | A_nexp nexp -> A_aux (A_nexp (expand_nexp_synonyms env nexp), l)
    | arg -> A_aux (arg, l)

  and add_constraint constr env =
    let (NC_aux (nc_aux, l) as constr) = constraint_simp (expand_constraint_synonyms env constr) in
    wf_constraint env constr;
    let power_vars = constraint_power_variables constr in
    if KidSet.cardinal power_vars > 1 && !opt_smt_linearize then
      typ_error env l ("Cannot add constraint " ^ string_of_n_constraint constr
                       ^ " where more than two variables appear within an exponential")
    else if KidSet.cardinal power_vars = 1 && !opt_smt_linearize then
      let v = KidSet.choose power_vars in
      let constrs = List.fold_left nc_and nc_true (get_constraints env) in
      begin match Constraint.solve_all_smt l constrs v with
      | Some solutions ->
         typ_print (lazy (Util.("Linearizing " |> red |> clear) ^ string_of_n_constraint constr
                          ^ " for " ^ string_of_kid v ^ " in " ^ Util.string_of_list ", " Big_int.to_string solutions));
         let linearized =
           List.fold_left
             (fun c s -> nc_or c (nc_and (nc_eq (nvar v) (nconstant s)) (constraint_subst v (arg_nexp (nconstant s)) constr)))
             nc_false solutions
         in
         typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint linearized));
         { env with constraints = linearized :: env.constraints }
      | None ->
         typ_error env l ("Type variable " ^ string_of_kid v
                          ^ " must have a finite number of solutions to add " ^ string_of_n_constraint constr)
      end
    else
      match nc_aux with
      | NC_true -> env
      | _ ->
         typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint constr));
         { env with constraints = constr :: env.constraints }

  let add_typquant l quant env =
    let rec add_quant_item env = function
      | QI_aux (qi, _) -> add_quant_item_aux env qi
    and add_quant_item_aux env = function
      | QI_constraint constr -> add_constraint constr env
      | QI_constant _ -> env
      | QI_id kopt -> add_typ_var l kopt env
    in
    match quant with
    | TypQ_aux (TypQ_no_forall, _) -> env
    | TypQ_aux (TypQ_tq quants, _) -> List.fold_left add_quant_item env quants

  let wf_typ env (Typ_aux (_, l) as typ) =
    let typ = expand_synonyms env typ in
    wf_debug "typ" string_of_typ typ KidSet.empty;
    incr depth;
    try
      wf_typ' env typ;
      decr depth
    with
    | Type_error (env, err_l, err) ->
       decr depth;
       typ_raise env l (Err_because (Err_other "Well-formedness check failed for type",
                                     err_l,
                                     err))
 
  let add_typ_synonym id typq arg env =
    if bound_typ_id env id then (
      typ_error env (id_loc id) ("Cannot define type synonym " ^ string_of_id id ^ ", as a type or synonym with that name already exists")
    ) else (
      let typq =
        quant_map_items (function
            | QI_aux (QI_constraint nexp, aux) -> QI_aux (QI_constraint (expand_constraint_synonyms env nexp), aux)
            | quant_item -> quant_item
          ) typq in
      typ_print (lazy (adding ^ "type synonym " ^ string_of_id id ^ ", " ^ string_of_typquant typq ^ " = " ^ string_of_typ_arg arg));
      { env with typ_synonyms = Bindings.add id (typq, expand_arg_synonyms (add_typquant (id_loc id) typq env) arg) env.typ_synonyms }
    )
                          
  let counter = ref 0

  let fresh_kid ?kid:(kid=mk_kid "") env =
    let suffix = if Kid.compare kid (mk_kid "") = 0 then "#" else "#" ^ string_of_id (id_of_kid kid) in
    let fresh = Kid_aux (Var ("'fv" ^ string_of_int !counter ^ suffix), Parse_ast.Unknown) in
    incr counter; fresh

  let freshen_kid env kid (typq, typ) =
    let fresh = fresh_kid ~kid:kid env in
    if KidSet.mem kid (KidSet.of_list (List.map kopt_kid (quant_kopts typq))) then
      (typquant_subst_kid kid fresh typq, subst_kid typ_subst kid fresh typ)
    else
      (typq, typ)

  let freshen_bind env bind =
    List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)

  let get_val_spec_orig id env =
    try
      Bindings.find id env.top_val_specs
    with
    | Not_found -> typ_error env (id_loc id) ("No type signature found for " ^ string_of_id id)

  let get_val_spec id env =
    try
      let bind = Bindings.find id env.top_val_specs in
      typ_debug (lazy ("get_val_spec: Env has " ^ string_of_list ", " (fun (kid, (_, k)) -> string_of_kid kid ^ " => " ^ string_of_kind_aux k) (KBindings.bindings env.typ_vars)));
      let bind' = List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars) in
      typ_debug (lazy ("get_val_spec: freshened to " ^ string_of_bind bind'));
      bind'
    with
    | Not_found -> typ_error env (id_loc id) ("No type declaration found for " ^ string_of_id id)

  let get_val_specs env = env.top_val_specs
                 
  let add_union_id id bind env =
    if bound_ctor_fn env id
    then typ_error env (id_loc id) ("A union constructor or function already exists with name " ^ string_of_id id )
    else
      begin
        typ_print (lazy (adding ^ "union identifier " ^ string_of_id id ^ " : " ^ string_of_bind bind));
        { env with union_ids = Bindings.add id bind env.union_ids }
      end
    
  let get_union_id id env =
    try
      let bind = Bindings.find id env.union_ids in
      List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars)
    with
    | Not_found -> typ_error env (id_loc id) ("No union constructor found for " ^ string_of_id id)

  let rec valid_implicits env start = function
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp (Nexp_aux (Nexp_var v, _)), _)]), l) :: rest ->
       if start then
         valid_implicits env true rest
       else
         typ_error env l "Arguments are invalid, implicit arguments must come before all other arguments"
    | Typ_aux (Typ_app (Id_aux (Id "implicit", _), [A_aux (A_nexp _, l)]), _) :: rest ->
       typ_error env l "Implicit argument must contain a single type variable"
    | _ :: rest -> valid_implicits env false rest
    | [] -> ()

  let rec update_val_spec id (typq, typ) env =
    let typq_env = add_typquant (id_loc id) typq env in
    begin match expand_synonyms typq_env typ with
    | Typ_aux (Typ_fn (arg_typs, ret_typ, effect), l) ->
       valid_implicits env true arg_typs;

       (* We perform some canonicalisation for function types where existentials appear on the left, so
          ({'n, 'n >= 2, int('n)}, foo) -> bar
          would become
          forall 'n, 'n >= 2. (int('n), foo) -> bar
          this enforces the invariant that all things on the left of functions are 'base types' (i.e. without existentials)
        *)
       let base_args = List.map (fun typ -> destruct_exist (expand_synonyms typq_env typ)) arg_typs in
       let existential_arg typq = function
         | None -> typq
         | Some (exs, nc, _) ->
            List.fold_left (fun typq kopt -> quant_add (mk_qi_kopt kopt) typq) (quant_add (mk_qi_nc nc) typq) exs
       in
       let typq = List.fold_left existential_arg typq base_args in
       let arg_typs = List.map2 (fun typ -> function Some (_, _, typ) -> typ | None -> typ) arg_typs base_args in
       let typ = Typ_aux (Typ_fn (arg_typs, ret_typ, effect), l) in
       typ_print (lazy (adding ^ "val " ^ string_of_id id ^ " : " ^ string_of_bind (typq, typ)));
       { env with top_val_specs = Bindings.add id (typq, typ) env.top_val_specs }

    | Typ_aux (Typ_bidir (typ1, typ2, effect), l) ->
       let env = add_mapping id (typq, typ1, typ2, effect) env in
       typ_print (lazy (adding ^ "mapping " ^ string_of_id id ^ " : " ^ string_of_bind (typq, typ)));
       { env with top_val_specs = Bindings.add id (typq, typ) env.top_val_specs }

    | _ -> typ_error env (id_loc id) "val definition must have a mapping or function type"
    end

  and add_val_spec id (bind_typq, bind_typ) env =
    if not (Bindings.mem id env.top_val_specs)
    then update_val_spec id (bind_typq, bind_typ) env
    else env

  and add_outcome id (typq, typ, params) env =
    { env with top_outcomes = Bindings.add id (typq, typ, params) env.top_outcomes }

  and get_outcome l id env =
    match Bindings.find_opt id env.top_outcomes with
    | Some outcome -> outcome
    | None ->
       typ_error env l ("Outcome " ^ string_of_id id ^ " does not exist")
    
  and add_mapping id (typq, typ1, typ2, effect) env =
    typ_print (lazy (adding ^ "mapping " ^ string_of_id id));
    let forwards_id = mk_id (string_of_id id ^ "_forwards") in
    let forwards_matches_id = mk_id (string_of_id id ^ "_forwards_matches") in
    let backwards_id = mk_id (string_of_id id ^ "_backwards") in
    let backwards_matches_id = mk_id (string_of_id id ^ "_backwards_matches") in
    let forwards_typ = Typ_aux (Typ_fn ([typ1], typ2, effect), Parse_ast.Unknown) in
    let forwards_matches_typ = Typ_aux (Typ_fn ([typ1], bool_typ, effect), Parse_ast.Unknown) in
    let backwards_typ = Typ_aux (Typ_fn ([typ2], typ1, effect), Parse_ast.Unknown) in
    let backwards_matches_typ = Typ_aux (Typ_fn ([typ2], bool_typ, effect), Parse_ast.Unknown) in
    let env =
      { env with mappings = Bindings.add id (typq, typ1, typ2) env.mappings }
      |> add_val_spec forwards_id (typq, forwards_typ)
      |> add_val_spec backwards_id (typq, backwards_typ)
      |> add_val_spec forwards_matches_id (typq, forwards_matches_typ)
      |> add_val_spec backwards_matches_id (typq, backwards_matches_typ)
    in
    let prefix_id = mk_id (string_of_id id ^ "_matches_prefix") in
    if strip_typ typ1 = string_typ then
      let forwards_prefix_typ = Typ_aux (Typ_fn ([typ1], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ2; nat_typ]), Parse_ast.Unknown)], no_effect), Parse_ast.Unknown) in
      add_val_spec prefix_id (typq, forwards_prefix_typ) env
    else if strip_typ typ2 = string_typ then
      let backwards_prefix_typ = Typ_aux (Typ_fn ([typ2], app_typ (mk_id "option") [A_aux (A_typ (tuple_typ [typ1; nat_typ]), Parse_ast.Unknown)], no_effect), Parse_ast.Unknown) in
      add_val_spec prefix_id (typq, backwards_prefix_typ) env
    else
      env

  let define_val_spec id env =
    if IdSet.mem id env.defined_val_specs
    then typ_error env (id_loc id) ("Function " ^ string_of_id id ^ " has already been declared")
    else { env with defined_val_specs = IdSet.add id env.defined_val_specs }

  let get_defined_val_specs env = env.defined_val_specs

  let is_union_constructor id env =
    let is_ctor id (Tu_aux (tu, _)) = match tu with
      | Tu_ty_id (_, ctor_id) when Id.compare id ctor_id = 0 -> true
      | _ -> false
    in
    let type_unions = List.concat (List.map (fun (_, (_, tus)) -> tus) (Bindings.bindings env.variants)) in
    List.exists (is_ctor id) type_unions

  let is_singleton_union_constructor id env =
    let is_ctor id (Tu_aux (tu, _)) = match tu with
      | Tu_ty_id (_, ctor_id) when Id.compare id ctor_id = 0 -> true
      | _ -> false
    in
    let type_unions = List.map (fun (_, (_, tus)) -> tus) (Bindings.bindings env.variants) in
    match List.find (List.exists (is_ctor id)) type_unions with
    | l -> List.length l = 1
    | exception Not_found -> false

  let is_mapping id env = Bindings.mem id env.mappings

  let add_enum id ids env =
    if bound_typ_id env id
    then typ_error env (id_loc id) ("Cannot create enum " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print (lazy (adding ^ "enum " ^ string_of_id id));
        { env with enums = Bindings.add id (IdSet.of_list ids) env.enums }
      end

  let get_enum id env =
    try IdSet.elements (Bindings.find id env.enums)
    with
    | Not_found -> typ_error env (id_loc id) ("Enumeration " ^ string_of_id id ^ " does not exist")

  let get_enums env = env.enums

  let is_enum id env = Bindings.mem id env.enums

  let is_record id env = Bindings.mem id env.records

  let get_record id env = Bindings.find id env.records
                        
  let get_records env = env.records
                        
  let add_record id typq fields env =
    if bound_typ_id env id
    then typ_error env (id_loc id) ("Cannot create record " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print (lazy (adding ^ "record " ^ string_of_id id));
        let rec record_typ_args = function
          | [] -> []
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_int_kopt kopt ->
             mk_typ_arg (A_nexp (nvar (kopt_kid kopt))) :: record_typ_args qis
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_typ_kopt kopt ->
             mk_typ_arg (A_typ (mk_typ (Typ_var (kopt_kid kopt)))) :: record_typ_args qis
          | ((QI_aux (QI_id kopt, _)) :: qis) when is_order_kopt kopt ->
             mk_typ_arg (A_order (mk_ord (Ord_var (kopt_kid kopt)))) :: record_typ_args qis
          | (_ :: qis) -> record_typ_args qis
        in
        let rectyp = match record_typ_args (quant_items typq) with
          | [] -> mk_id_typ id
          | args -> mk_typ (Typ_app (id, args))
        in
        let fold_accessors accs (typ, fid) =
          let acc_typ = mk_typ (Typ_fn ([rectyp], typ, Effect_aux (Effect_set [], Parse_ast.Unknown))) in
          typ_print (lazy (indent 1 ^ adding ^ "accessor " ^ string_of_id id ^ "." ^ string_of_id fid ^ " :: " ^ string_of_bind (typq, acc_typ)));
          Bindings.add (field_name id fid) (typq, acc_typ) accs
        in
        { env with records = Bindings.add id (typq, fields) env.records;
                   accessors = List.fold_left fold_accessors env.accessors fields }
      end

  let get_accessor_fn rec_id id env =
    let freshen_bind bind = List.fold_left (fun bind (kid, _) -> freshen_kid env kid bind) bind (KBindings.bindings env.typ_vars) in
    try freshen_bind (Bindings.find (field_name rec_id id) env.accessors)
    with
    | Not_found -> typ_error env (id_loc id) ("No accessor found for " ^ string_of_id (field_name rec_id id))

  let get_accessor rec_id id env =
    match get_accessor_fn rec_id id env with
    (* All accessors should have a single argument (the record itself) *)
    | (typq, Typ_aux (Typ_fn ([rec_typ], field_typ, effect), _)) ->
       (typq, rec_typ, field_typ, effect)
    | _ -> typ_error env (id_loc id) ("Accessor with non-function type found for " ^ string_of_id (field_name rec_id id))

  let is_mutable id env =
    try
      let (mut, _) = Bindings.find id env.locals in
      match mut with
      | Mutable -> true
      | Immutable -> false
    with
    | Not_found -> false

  let string_of_mtyp (mut, typ) = match mut with
    | Immutable -> string_of_typ typ
    | Mutable -> "ref<" ^ string_of_typ typ ^ ">"

  let add_local id mtyp env =
    if not env.allow_bindings then typ_error env (id_loc id) "Bindings are not allowed in this context" else ();
    wf_typ env (snd mtyp);
    if Bindings.mem id env.top_val_specs then
      typ_error env (id_loc id) ("Local variable " ^ string_of_id id ^ " is already bound as a function name")
    else ();
    typ_print (lazy (adding ^ "local binding " ^ string_of_id id ^ " : " ^ string_of_mtyp mtyp));
    { env with locals = Bindings.add id mtyp env.locals;
               top_letbinds = IdSet.remove id env.top_letbinds }

  let add_toplevel_lets ids env =
    { env with top_letbinds = IdSet.union ids env.top_letbinds }

  let get_toplevel_lets env = env.top_letbinds

  let add_variant id variant env =
    if bound_typ_id env id
    then typ_error env (id_loc id) ("Cannot create variant " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print (lazy (adding ^ "variant " ^ string_of_id id));
        { env with variants = Bindings.add id variant env.variants }
      end
    
  let add_scattered_variant id typq env =
    if bound_typ_id env id
    then typ_error env (id_loc id) ("Cannot create scattered variant " ^ string_of_id id ^ ", type name is already bound")
    else
      begin
        typ_print (lazy (adding ^ "scattered variant " ^ string_of_id id));
        { env with
          variants = Bindings.add id (typq, []) env.variants;
          scattered_variant_envs = Bindings.add id env env.scattered_variant_envs
        }
      end

  let add_variant_clause id tu env =
    match Bindings.find_opt id env.variants with
    | Some (typq, tus) -> { env with variants = Bindings.add id (typq, tus @ [tu]) env.variants }
    | None -> typ_error env (id_loc id) ("scattered union " ^ string_of_id id ^ " not found")

  let get_variants env = env.variants
            
  let get_variant id env =
    match Bindings.find_opt id env.variants with
    | Some (typq, tus) -> typq, tus
    | None -> typ_error env (id_loc id) ("union " ^ string_of_id id ^ " not found")

  let get_scattered_variant_env id env =
    match Bindings.find_opt id env.scattered_variant_envs with
    | Some env' -> env'
    | None -> typ_error env (id_loc id) ("scattered union " ^ string_of_id id ^ " has not been declared")

  let is_register id env =
    Bindings.mem id env.registers

  let get_register id env =
    try Bindings.find id env.registers with
    | Not_found -> typ_error env (id_loc id) ("No register binding found for " ^ string_of_id id)

  let get_registers env = env.registers

  let is_extern id env backend =
    try not (Ast_util.extern_assoc backend (Bindings.find id env.externs) = None) with
    | Not_found -> false
    (* Bindings.mem id env.externs *)

  let add_extern id ext env =
    { env with externs = Bindings.add id ext env.externs }

  let get_extern id env backend =
    try
      match Ast_util.extern_assoc backend (Bindings.find id env.externs) with
      | Some ext -> ext
      | None -> typ_error env (id_loc id) ("No extern binding found for " ^ string_of_id id)
    with
    | Not_found -> typ_error env (id_loc id) ("No extern binding found for " ^ string_of_id id)

  let get_casts env = env.casts

  let add_register id reff weff typ env =
    wf_typ env typ;
    if Bindings.mem id env.registers
    then typ_error env (id_loc id) ("Register " ^ string_of_id id ^ " is already bound")
    else
      begin
        typ_print (lazy (adding ^ "register binding " ^ string_of_id id ^ " :: " ^ string_of_typ typ));
        { env with registers = Bindings.add id (reff, weff, typ) env.registers }
      end

  let get_locals env = env.locals

  let lookup_id ?raw:(raw=false) id env =
    try
      let (mut, typ) = Bindings.find id env.locals in
      Local (mut, typ)
    with
    | Not_found ->
    try
      let reff, weff, typ = Bindings.find id env.registers in
      Register (reff, weff, typ)
    with
    | Not_found ->
    try
      let (enum, _) = List.find (fun (enum, ctors) -> IdSet.mem id ctors) (Bindings.bindings env.enums) in
      Enum (mk_typ (Typ_id enum))
    with
    | Not_found -> Unbound

  let get_ret_typ env = env.ret_typ

  let add_ret_typ typ env = { env with ret_typ = Some typ }

  let allow_casts env = env.allow_casts

  let no_casts env = { env with allow_casts = false }
  let enable_casts env = { env with allow_casts = true }

  let no_bindings env = { env with allow_bindings = false }

  let add_cast cast env =
    typ_print (lazy (adding ^ "cast " ^ string_of_id cast));
    { env with casts = cast :: env.casts }

  let get_default_order env =
    match env.default_order with
    | None -> typ_error env Parse_ast.Unknown ("No default order has been set")
    | Some ord -> ord

  let get_default_order_option env = env.default_order
                
  let set_default_order o env =
    match o with
    | Ord_aux (Ord_var _, l) -> typ_error env l "Cannot have variable default order"
    | Ord_aux (_, l) ->
       match env.default_order with
       | None -> { env with default_order = Some o }
       | Some _ -> typ_error env l ("Cannot change default order once already set")

  let base_typ_of env typ =
    let rec aux (Typ_aux (t,a)) =
      let rewrap t = Typ_aux (t,a) in
      match t with
      | Typ_fn (arg_typs, ret_typ, eff) ->
        rewrap (Typ_fn (List.map aux arg_typs, aux ret_typ, eff))
      | Typ_tup ts ->
        rewrap (Typ_tup (List.map aux ts))
      | Typ_app (r, [A_aux (A_typ rtyp,_)]) when string_of_id r = "register" ->
        aux rtyp
      | Typ_app (id, targs) ->
        rewrap (Typ_app (id, List.map aux_arg targs))
      | t -> rewrap t
    and aux_arg (A_aux (targ,a)) =
      let rewrap targ = A_aux (targ,a) in
      match targ with
      | A_typ typ -> rewrap (A_typ (aux typ))
      | targ -> rewrap targ in
    aux (expand_synonyms env typ)

  let get_bitfield_range l id field env =
    match Bindings.find_opt id env.bitfields with
    | Some ranges ->
       begin match Bindings.find_opt field ranges with
       | Some range -> range
       | None -> typ_error env l (Printf.sprintf "Field %s does not exist in the bitfield %s" (string_of_id field) (string_of_id id))
       end
    | None -> typ_error env l (Printf.sprintf "%s is not a bitfield" (string_of_id id))

  let add_bitfield id ranges env =
    { env with bitfields = Bindings.add id ranges env.bitfields }

  let allow_polymorphic_undefineds env =
    { env with poly_undefineds = true }

  let polymorphic_undefineds env = env.poly_undefineds

end

let expand_bind_synonyms l env (typq, typ) =
  typq, Env.expand_synonyms (Env.add_typquant l typq env) typ

let wf_binding l env (typq, typ) =
  let env = Env.add_typquant l typq env in
  Env.wf_typ env typ

let wf_typschm env (TypSchm_aux (TypSchm_ts (typq, typ), l)) = wf_binding l env (typq, typ)

(* Create vectors with the default order from the environment *)

let default_order_error_string =
  "No default Order (if you have set a default Order, move it earlier in the specification)"

let dvector_typ env n typ = vector_typ n (Env.get_default_order env) typ
let bits_typ env n = bitvector_typ n (Env.get_default_order env)

let add_existential l kopts nc env =
  let env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) env kopts in
  Env.add_constraint nc env

let add_typ_vars l kopts env = List.fold_left (fun env kopt -> Env.add_typ_var l kopt env) env kopts

let is_exist = function
  | Typ_aux (Typ_exist (_, _, _), _) -> true
  | _ -> false

let exist_typ constr typ =
  let fresh = fresh_existential K_int in
  mk_typ (Typ_exist ([fresh], constr (kopt_kid fresh), typ (kopt_kid fresh)))

let bind_numeric l typ env =
  match destruct_numeric (Env.expand_synonyms env typ) with
  | Some (kids, nc, nexp) ->
     nexp, add_existential l (List.map (mk_kopt K_int) kids) nc env
  | None -> typ_error env l ("Expected " ^ string_of_typ typ ^ " to be numeric")

let rec check_shadow_leaks l inner_env outer_env typ =
  typ_debug (lazy ("Shadow leaks: " ^ string_of_typ typ));
  let vars = tyvars_of_typ typ in
  List.iter (fun var ->
      if Env.shadows var inner_env > Env.shadows var outer_env then
        typ_error outer_env l
          ("Type variable " ^ string_of_kid var ^ " would leak into a scope where it is shadowed")
      else
        match Env.get_typ_var_loc_opt var outer_env with
        | Some _ -> ()
        | None ->
           match Env.get_typ_var_loc_opt var inner_env with
           | Some leak_l ->
              typ_raise outer_env l
                (Err_because
                   (Err_other ("The type variable " ^ string_of_kid var
                               ^ " would leak into an outer scope.\n\nTry adding a type annotation to this expression."),
                    leak_l,
                    Err_other ("Type variable " ^ string_of_kid var ^ " was introduced here")))
           | None -> Reporting.unreachable l __POS__ "Found a type with an unknown type variable"
    )
    (KidSet.elements vars);
  typ
   
(** Pull an (potentially)-existentially qualified type into the global
   typing environment **)
let bind_existential l name typ env =
  match destruct_exist ~name:name (Env.expand_synonyms env typ) with
  | Some (kids, nc, typ) -> typ, add_existential l kids nc env
  | None -> typ, env

let bind_tuple_existentials l name (Typ_aux (aux, annot) as typ) env =
  match aux with
  | Typ_tup typs ->
     let typs, env =
       List.fold_right (fun typ (typs, env) -> let typ, env = bind_existential l name typ env in typ :: typs, env) typs ([], env)
     in
     Typ_aux (Typ_tup typs, annot), env
  | _ -> typ, env

let destruct_range env typ =
  let kopts, constr, (Typ_aux (typ_aux, _)) =
    Util.option_default ([], nc_true, typ) (destruct_exist (Env.expand_synonyms env typ))
  in
  match typ_aux with
    | Typ_app (f, [A_aux (A_nexp n, _)])
         when string_of_id f = "atom" || string_of_id f = "implicit" -> Some (List.map kopt_kid kopts, constr, n, n)
    | Typ_app (f, [A_aux (A_nexp n1, _); A_aux (A_nexp n2, _)])
         when string_of_id f = "range" -> Some (List.map kopt_kid kopts, constr, n1, n2)
    | _ -> None

let destruct_vector env typ =
  let destruct_vector' = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _);
                             A_aux (A_typ vtyp, _)]
                       ), _) when string_of_id id = "vector" -> Some (nexp_simp n1, o, vtyp)
    | typ -> None
  in
  destruct_vector' (Env.expand_synonyms env typ)

let destruct_bitvector env typ =
  let destruct_bitvector' = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _)]
                       ), _) when string_of_id id = "bitvector" -> Some (nexp_simp n1, o)
    | typ -> None
  in
  destruct_bitvector' (Env.expand_synonyms env typ)

let rec is_typ_monomorphic (Typ_aux (typ, l)) =
  match typ with
  | Typ_id _ -> true
  | Typ_tup typs -> List.for_all is_typ_monomorphic typs
  | Typ_app (id, args) -> List.for_all is_typ_arg_monomorphic args
  | Typ_fn (arg_typs, ret_typ, _) -> List.for_all is_typ_monomorphic arg_typs && is_typ_monomorphic ret_typ
  | Typ_bidir (typ1, typ2, _) -> is_typ_monomorphic typ1 && is_typ_monomorphic typ2
  | Typ_exist _ | Typ_var _ -> false
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
and is_typ_arg_monomorphic (A_aux (arg, _)) =
  match arg with
  | A_nexp _ -> true
  | A_typ typ -> is_typ_monomorphic typ
  | A_bool _ -> true
  | A_order (Ord_aux (Ord_dec, _)) | A_order (Ord_aux (Ord_inc, _)) -> true
  | A_order (Ord_aux (Ord_var _, _)) -> false

(**************************************************************************)
(* 2. Subtyping and constraint solving                                    *)
(**************************************************************************)

type ('a, 'b) filter =
  | Keep of 'a
  | Remove of 'b

let rec filter_keep = function
  | Keep x :: xs -> x :: filter_keep xs
  | Remove _ :: xs -> filter_keep xs
  | [] -> []

let rec filter_remove = function
  | Keep _ :: xs -> filter_remove xs
  | Remove x :: xs -> x :: filter_remove xs
  | [] -> []

let filter_split f g xs =
  let xs = List.map f xs in
  filter_keep xs, g (filter_remove xs)

let rec simp_typ (Typ_aux (typ_aux, l)) = Typ_aux (simp_typ_aux typ_aux, l)
and simp_typ_aux = function
  | Typ_exist (kids1, nc1, Typ_aux (Typ_exist (kids2, nc2, typ), _)) ->
     simp_typ_aux (Typ_exist (kids1 @ kids2, nc_and nc1 nc2, typ))

  (* This removes redundant boolean variables in existentials, such
     that {('p: Bool) ('q:Bool) ('r: Bool), nc('r). bool('p & 'q & 'r)}
     would become {('s:Bool) ('r: Bool), nc('r). bool('s & 'r)},
     wherein all the redundant boolean variables have been combined
     into a single one. Making this simplification allows us to avoid
     having to pass large numbers of pointless variables to SMT if we
     ever bind this existential. *)
  | Typ_exist (vars, nc, Typ_aux (Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool b, _)]), _)) ->
     let kids = KidSet.of_list (List.map kopt_kid vars) in
     let constrained = tyvars_of_constraint nc in
     let conjs = constraint_conj b in
     let is_redundant = function
       | NC_aux (NC_var v, _) when KidSet.mem v kids && not (KidSet.mem v constrained) -> Remove v
       | nc -> Keep nc
     in
     let conjs, redundant = filter_split is_redundant KidSet.of_list conjs in
     begin match conjs with
     | [] -> Typ_id (mk_id "bool")
     | conj :: conjs when KidSet.is_empty redundant ->
        Typ_exist (vars, nc, atom_bool_typ (List.fold_left nc_and conj conjs))
     | conjs ->
        let vars = List.filter (fun v -> not (KidSet.mem (kopt_kid v) redundant)) vars in
        let var = fresh_existential K_bool in
        Typ_exist (var :: vars, nc, atom_bool_typ (List.fold_left nc_and (nc_var (kopt_kid var)) conjs))
     end

  | typ_aux -> typ_aux

(* Here's how the constraint generation works for subtyping

X(b,c...) --> {a. Y(a,b,c...)} \subseteq {a. Z(a,b,c...)}

this is equivalent to

\forall b c. X(b,c) --> \forall a. Y(a,b,c) --> Z(a,b,c)

\forall b c. X(b,c) --> \forall a. !Y(a,b,c) \/ !Z^-1(a,b,c)

\forall b c. X(b,c) --> !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

\forall b c. !X(b,c) \/ !\exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists b c. X(b,c) /\ \exists a. Y(a,b,c) /\ Z^-1(a,b,c)

!\exists a b c. X(b,c) /\ Y(a,b,c) /\ Z^-1(a,b,c)

which is then a problem we can feed to the constraint solver expecting unsat.
 *)

let prove_smt env (NC_aux (_, l) as nc) =
  let ncs = Env.get_constraints env in
  match Constraint.call_smt l (List.fold_left nc_and (nc_not nc) ncs) with
  | Constraint.Unsat -> typ_debug (lazy "unsat"); true
  | Constraint.Sat -> typ_debug (lazy "sat"); false
  | Constraint.Unknown ->
     (* Work around versions of z3 that are confused by 2^n in
        constraints, even when such constraints are irrelevant *)
     let ncs' = List.concat (List.map constraint_conj ncs) in
     let ncs' = List.filter (fun nc -> KidSet.is_empty (constraint_power_variables nc)) ncs' in
     match Constraint.call_smt l (List.fold_left nc_and (nc_not nc) ncs') with
     | Constraint.Unsat -> typ_debug (lazy "unsat"); true
     | Constraint.Sat | Constraint.Unknown -> typ_debug (lazy "sat/unknown"); false

let solve_unique env (Nexp_aux (_, l) as nexp) =
  typ_print (lazy (Util.("Solve " |> red |> clear) ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env)
                   ^ " |- " ^ string_of_nexp nexp ^ " = ?"));
  match nexp with
  | Nexp_aux (Nexp_constant n,_) -> Some n
  | _ ->
    let env = Env.add_typ_var Parse_ast.Unknown (mk_kopt K_int (mk_kid "solve#")) env in
    let vars = Env.get_typ_vars env in
    let vars = KBindings.filter (fun _ k -> match k with K_int | K_bool -> true | _ -> false) vars in
    let constr = List.fold_left nc_and (nc_eq (nvar (mk_kid "solve#")) nexp) (Env.get_constraints env) in
    Constraint.solve_unique_smt l constr (mk_kid "solve#")

let debug_pos (file, line, _, _) =
  "(" ^ file ^ "/" ^ string_of_int line ^ ") "

let prove pos env nc =
  typ_print (lazy (Util.("Prove " |> red |> clear) ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_n_constraint nc));
  let (NC_aux (nc_aux, _) as nc) = constraint_simp (Env.expand_constraint_synonyms env nc) in
  if !Constraint.opt_smt_verbose then
    prerr_endline (Util.("Prove " |> red |> clear) ^ debug_pos pos ^ string_of_list ", " string_of_n_constraint (Env.get_constraints env) ^ " |- " ^ string_of_n_constraint nc)
  else ();
  match nc_aux with
  | NC_true -> true
  | _ -> prove_smt env nc

(**************************************************************************)
(* 3. Unification                                                         *)
(**************************************************************************)

let rec nexp_frees ?exs:(exs=KidSet.empty) (Nexp_aux (nexp, l)) =
  match nexp with
  | Nexp_id _ -> KidSet.empty
  | Nexp_var kid -> KidSet.singleton kid
  | Nexp_constant _ -> KidSet.empty
  | Nexp_times (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_sum (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_minus (n1, n2) -> KidSet.union (nexp_frees ~exs:exs n1) (nexp_frees ~exs:exs n2)
  | Nexp_app (id, ns) -> List.fold_left KidSet.union KidSet.empty (List.map (fun n -> nexp_frees ~exs:exs n) ns)
  | Nexp_exp n -> nexp_frees ~exs:exs n
  | Nexp_neg n -> nexp_frees ~exs:exs n

let rec nexp_identical (Nexp_aux (nexp1, _)) (Nexp_aux (nexp2, _)) =
  match nexp1, nexp2 with
  | Nexp_id v1, Nexp_id v2 -> Id.compare v1 v2 = 0
  | Nexp_var kid1, Nexp_var kid2 -> Kid.compare kid1 kid2 = 0
  | Nexp_constant c1, Nexp_constant c2 -> Big_int.equal c1 c2
  | Nexp_times (n1a, n1b), Nexp_times (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_sum (n1a, n1b), Nexp_sum (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_minus (n1a, n1b), Nexp_minus (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | Nexp_exp n1, Nexp_exp n2 -> nexp_identical n1 n2
  | Nexp_neg n1, Nexp_neg n2 -> nexp_identical n1 n2
  | Nexp_app (f1, args1), Nexp_app (f2, args2) when List.length args1 = List.length args2 ->
     Id.compare f1 f2 = 0 && List.for_all2 nexp_identical args1 args2
  | _, _ -> false

let ord_identical (Ord_aux (ord1, _)) (Ord_aux (ord2, _)) =
  match ord1, ord2 with
  | Ord_var kid1, Ord_var kid2 -> Kid.compare kid1 kid2 = 0
  | Ord_inc, Ord_inc -> true
  | Ord_dec, Ord_dec -> true
  | _, _ -> false

let rec nc_identical (NC_aux (nc1, _)) (NC_aux (nc2, _)) =
  match nc1, nc2 with
  | NC_equal (n1a, n1b), NC_equal (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_not_equal (n1a, n1b), NC_not_equal (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_ge (n1a, n1b), NC_bounded_ge (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_gt (n1a, n1b), NC_bounded_gt (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_le (n1a, n1b), NC_bounded_le (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_bounded_lt (n1a, n1b), NC_bounded_lt (n2a, n2b) -> nexp_identical n1a n2a && nexp_identical n1b n2b
  | NC_or (nc1a, nc1b), NC_or (nc2a, nc2b) -> nc_identical nc1a nc2a && nc_identical nc1b nc2b
  | NC_and (nc1a, nc1b), NC_and (nc2a, nc2b) -> nc_identical nc1a nc2a && nc_identical nc1b nc2b
  | NC_true, NC_true -> true
  | NC_false, NC_false -> true
  | NC_set (kid1, ints1), NC_set (kid2, ints2) when List.length ints1 = List.length ints2 ->
     Kid.compare kid1 kid2 = 0 && List.for_all2 (fun i1 i2 -> i1 = i2) ints1 ints2
  | NC_var kid1, NC_var kid2 -> Kid.compare kid1 kid2 = 0
  | NC_app (id1, args1), NC_app (id2, args2) when List.length args1 = List.length args2 ->
     Id.compare id1 id2 = 0 && List.for_all2 typ_arg_identical args1 args2
  | _, _ -> false

and typ_arg_identical (A_aux (arg1, _)) (A_aux (arg2, _)) =
  match arg1, arg2 with
  | A_nexp n1, A_nexp n2 -> nexp_identical n1 n2
  | A_typ typ1, A_typ typ2 -> typ_identical typ1 typ2
  | A_order ord1, A_order ord2 -> ord_identical ord1 ord2
  | A_bool nc1, A_bool nc2 -> nc_identical nc1 nc2
  | _, _ -> false

and typ_identical (Typ_aux (typ1, _)) (Typ_aux (typ2, _)) =
  match typ1, typ2 with
  | Typ_id v1, Typ_id v2 -> Id.compare v1 v2 = 0
  | Typ_var kid1, Typ_var kid2 -> Kid.compare kid1 kid2 = 0
  | Typ_fn (arg_typs1, ret_typ1, eff1), Typ_fn (arg_typs2, ret_typ2, eff2)
       when List.length arg_typs1 = List.length arg_typs2 ->
     List.for_all2 typ_identical arg_typs1 arg_typs2
     && typ_identical ret_typ1 ret_typ2
     && strip_effect eff1 = strip_effect eff2
  | Typ_bidir (typ1, typ2, eff1), Typ_bidir (typ3, typ4, eff2) ->
     typ_identical typ1 typ3
     && typ_identical typ2 typ4
     && strip_effect eff1 = strip_effect eff2
  | Typ_tup typs1, Typ_tup typs2 ->
     begin
       try List.for_all2 typ_identical typs1 typs2 with
       | Invalid_argument _ -> false
     end
  | Typ_app (f1, args1), Typ_app (f2, args2) ->
     begin
       try Id.compare f1 f2 = 0 && List.for_all2 typ_arg_identical args1 args2 with
       | Invalid_argument _ -> false
     end
  | Typ_exist (kopts1, nc1, typ1), Typ_exist (kopts2, nc2, typ2) when List.length kopts1 = List.length kopts2 ->
     List.for_all2 (fun k1 k2 -> KOpt.compare k1 k2 = 0) kopts1 kopts2 && nc_identical nc1 nc2 && typ_identical typ1 typ2
  | _, _ -> false

let expanded_typ_identical env typ1 typ2 =
  typ_identical (Env.expand_synonyms env typ1) (Env.expand_synonyms env typ2)

exception Unification_error of l * string;;

let unify_error l str = raise (Unification_error (l, str))

let merge_unifiers l kid uvar1 uvar2 =
  match uvar1, uvar2 with
  | Some arg1, Some arg2 ->
     if typ_arg_identical arg1 arg2 then
       Some arg1
     else
       unify_error l ("Multiple non-identical unifiers for " ^ string_of_kid kid
                      ^ ": " ^ string_of_typ_arg arg1 ^ " and " ^ string_of_typ_arg arg2)
  | None, Some u2 -> Some u2
  | Some u1, None -> Some u1
  | None, None -> None

let merge_uvars l unifiers1 unifiers2 =
  KBindings.merge (merge_unifiers l) unifiers1 unifiers2

let rec unify_typ l env goals (Typ_aux (aux1, _) as typ1) (Typ_aux (aux2, _) as typ2) =
  typ_debug (lazy (Util.("Unify type " |> magenta |> clear) ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2
                   ^ " goals " ^ string_of_list ", " string_of_kid (KidSet.elements goals)));
  match aux1, aux2 with
  | Typ_internal_unknown, _ | _, Typ_internal_unknown
       when Env.allow_unknowns env ->
     KBindings.empty

  | Typ_var v, _ when KidSet.mem v goals -> KBindings.singleton v (arg_typ typ2)

  | Typ_var v1, Typ_var v2 when Kid.compare v1 v2 = 0 -> KBindings.empty

  (* We need special cases for unifying range(n, m), nat, and int vs atom('n) *)
  | Typ_id int, Typ_app (atom, [A_aux (A_nexp n, _)]) when string_of_id int = "int" -> KBindings.empty

  | Typ_id nat, Typ_app (atom, [A_aux (A_nexp n, _)]) when string_of_id nat = "nat" ->
     if prove __POS__ env (nc_gteq n (nint 0)) then KBindings.empty
     else unify_error l (string_of_typ typ2 ^ " must be a natural number")

  | Typ_app (range, [A_aux (A_nexp n1, _); A_aux (A_nexp n2, _)]),
    Typ_app (atom, [A_aux (A_nexp m, _)])
       when string_of_id range = "range" && string_of_id atom = "atom" ->
     let n1, n2 = nexp_simp n1, nexp_simp n2 in
     begin match n1, n2 with
     | Nexp_aux (Nexp_constant c1, _), Nexp_aux (Nexp_constant c2, _) ->
        if prove __POS__ env (nc_and (nc_lteq n1 m) (nc_lteq m n2)) then KBindings.empty
        else unify_error l (string_of_typ typ1 ^ " is not contained within " ^ string_of_typ typ1)
     | _, _ ->
        merge_uvars l (unify_nexp l env goals n1 m) (unify_nexp l env goals n2 m)
     end

  | Typ_app (id1, args1), Typ_app (id2, args2) when List.length args1 = List.length args2 && Id.compare id1 id2 = 0 ->
     List.fold_left (merge_uvars l) KBindings.empty (List.map2 (unify_typ_arg l env goals) args1 args2)

  | Typ_app (id1, []), Typ_id id2 when Id.compare id1 id2 = 0 -> KBindings.empty
  | Typ_id id1, Typ_app (id2, []) when Id.compare id1 id2 = 0 -> KBindings.empty
  | Typ_id id1, Typ_id id2 when Id.compare id1 id2 = 0 -> KBindings.empty

  | Typ_tup typs1, Typ_tup typs2 when List.length typs1 = List.length typs2 ->
     List.fold_left (merge_uvars l) KBindings.empty (List.map2 (unify_typ l env goals) typs1 typs2)

  | _, _ -> unify_error l ("Could not unify " ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2)

and unify_typ_arg l env goals (A_aux (aux1, _) as typ_arg1) (A_aux (aux2, _) as typ_arg2) =
  match aux1, aux2 with
  | A_typ typ1, A_typ typ2 -> unify_typ l env goals typ1 typ2
  | A_nexp nexp1, A_nexp nexp2 -> unify_nexp l env goals nexp1 nexp2
  | A_order ord1, A_order ord2 -> unify_order l goals ord1 ord2
  | A_bool nc1, A_bool nc2 -> unify_constraint l env goals nc1 nc2
  | _, _ -> unify_error l ("Could not unify type arguments " ^ string_of_typ_arg typ_arg1 ^ " and " ^ string_of_typ_arg typ_arg2)

and unify_constraint l env goals (NC_aux (aux1, _) as nc1) (NC_aux (aux2, _) as nc2) =
  typ_debug (lazy (Util.("Unify constraint " |> magenta |> clear) ^ string_of_n_constraint nc1 ^ " and " ^ string_of_n_constraint nc2));
  match aux1, aux2 with
  | NC_var v, _ when KidSet.mem v goals -> KBindings.singleton v (arg_bool nc2)
  | NC_var v, NC_var v' when Kid.compare v v' = 0 -> KBindings.empty
  | NC_and (nc1a, nc2a), NC_and (nc1b, nc2b) ->
     begin
       try
         let conjs1 = List.sort NC.compare (constraint_conj nc1) in
         let conjs2 = List.sort NC.compare (constraint_conj nc2) in
         let unify_merge uv nc1 nc2 = merge_uvars l uv (unify_constraint l env goals nc1 nc2) in
         List.fold_left2 unify_merge KBindings.empty conjs1 conjs2
       with
       | _ -> merge_uvars l (unify_constraint l env goals nc1a nc1b) (unify_constraint l env goals nc2a nc2b)
     end
  | NC_or (nc1a, nc2a), NC_or (nc1b, nc2b) ->
     merge_uvars l (unify_constraint l env goals nc1a nc1b) (unify_constraint l env goals nc2a nc2b)
  | NC_app (f1, args1), NC_app (f2, args2) when Id.compare f1 f2 = 0 && List.length args1 = List.length args2 ->
     List.fold_left (merge_uvars l) KBindings.empty (List.map2 (unify_typ_arg l env goals) args1 args2)
  | NC_equal (n1a, n2a), NC_equal (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_not_equal (n1a, n2a), NC_not_equal (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_ge (n1a, n2a), NC_bounded_ge (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_gt (n1a, n2a), NC_bounded_gt (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_le (n1a, n2a), NC_bounded_le (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_bounded_lt (n1a, n2a), NC_bounded_lt (n1b, n2b) ->
     merge_uvars l (unify_nexp l env goals n1a n1b) (unify_nexp l env goals n2a n2b)
  | NC_true, NC_true -> KBindings.empty
  | NC_false, NC_false -> KBindings.empty
  | _, _ -> unify_error l ("Could not unify constraints " ^ string_of_n_constraint nc1 ^ " and " ^ string_of_n_constraint nc2)

and unify_order l goals (Ord_aux (aux1, _) as ord1) (Ord_aux (aux2, _) as ord2) =
  typ_print (lazy (Util.("Unify order " |> magenta |> clear) ^ string_of_order ord1 ^ " and " ^ string_of_order ord2));
  match aux1, aux2 with
  | Ord_var v, _ when KidSet.mem v goals -> KBindings.singleton v (arg_order ord2)
  | Ord_inc, Ord_inc -> KBindings.empty
  | Ord_dec, Ord_dec -> KBindings.empty
  | _, _ -> unify_error l ("Could not unify " ^ string_of_order ord1 ^ " and " ^ string_of_order ord2)

and unify_nexp l env goals (Nexp_aux (nexp_aux1, _) as nexp1) (Nexp_aux (nexp_aux2, _) as nexp2) =
  typ_debug (lazy (Util.("Unify nexp " |> magenta |> clear) ^ string_of_nexp nexp1 ^ " and " ^ string_of_nexp nexp2
                   ^ " goals " ^ string_of_list ", " string_of_kid (KidSet.elements goals)));
  if KidSet.is_empty (KidSet.inter (nexp_frees nexp1) goals)
  then
    begin
      if prove __POS__ env (NC_aux (NC_equal (nexp1, nexp2), Parse_ast.Unknown))
      then KBindings.empty
      else unify_error l ("Nexp " ^ string_of_nexp nexp1 ^ " and " ^ string_of_nexp nexp2 ^ " are not equal")
    end
  else
    match nexp_aux1 with
    | Nexp_id v -> unify_error l "Unimplemented Nexp_id in unify nexp"
    | Nexp_var kid when KidSet.mem kid goals -> KBindings.singleton kid (arg_nexp nexp2)
    | Nexp_constant c1 ->
       begin
         match nexp_aux2 with
         | Nexp_constant c2 -> if c1 = c2 then KBindings.empty else unify_error l "Constants are not the same"
         | _ -> unify_error l "Unification error"
       end
    | Nexp_sum (n1a, n1b) ->
       if KidSet.is_empty (nexp_frees n1b)
       then unify_nexp l env goals n1a (nminus nexp2 n1b)
       else
         if KidSet.is_empty (nexp_frees n1a)
         then unify_nexp l env goals n1b (nminus nexp2 n1a)
         else begin
           match nexp_aux2 with
           | Nexp_sum (n2a, n2b) ->
              if KidSet.is_empty (nexp_frees n2a)
              then unify_nexp l env goals n2b (nminus nexp1 n2a)
              else
                if KidSet.is_empty (nexp_frees n2a)
                then unify_nexp l env goals n2a (nminus nexp1 n2b)
                else merge_uvars l (unify_nexp l env goals n1a n2a) (unify_nexp l env goals n1b n2b)
           | _ -> unify_error l ("Both sides of Int expression " ^ string_of_nexp nexp1
                               ^ " contain free type variables so it cannot be unified with " ^ string_of_nexp nexp2)
         end
    | Nexp_minus (n1a, n1b) ->
       if KidSet.is_empty (nexp_frees n1b)
       then unify_nexp l env goals n1a (nsum nexp2 n1b)
       else unify_error l ("Cannot unify minus Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | Nexp_times (n1a, n1b) ->
       (* If we have SMT operations div and mod, then we can use the
          property that

          mod(m, C) = 0 && C != 0 --> (C * n = m <--> n = m / C)

          to help us unify multiplications and divisions. *)
       let valid n c = prove __POS__ env (nc_eq (napp (mk_id "mod") [n; c]) (nint 0)) && prove __POS__ env (nc_neq c (nint 0)) in
       (*if KidSet.is_empty (nexp_frees n1b) && valid nexp2 n1b then
         unify_nexp l env goals n1a (napp (mk_id "div") [nexp2; n1b])
       else if KidSet.is_empty (nexp_frees n1a) && valid nexp2 n1a then
         unify_nexp l env goals n1b (napp (mk_id "div") [nexp2; n1a]) *)
       if KidSet.is_empty (nexp_frees n1a) then
         begin
           match nexp_aux2 with
           | Nexp_times (n2a, n2b) when prove __POS__ env (NC_aux (NC_equal (n1a, n2a), Parse_ast.Unknown)) ->
              unify_nexp l env goals n1b n2b
           | Nexp_constant c2 ->
              begin
                match n1a with
                | Nexp_aux (Nexp_constant c1,_) when Big_int.equal (Big_int.modulus c2 c1) Big_int.zero ->
                   unify_nexp l env goals n1b (nconstant (Big_int.div c2 c1))
                | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
              end
           | Nexp_var kid when (not (KidSet.mem kid goals)) && valid nexp2 n1a && !opt_smt_div ->
              unify_nexp l env goals n1b (napp (mk_id "div") [nexp2; n1a])
           | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
         end
       else if KidSet.is_empty (nexp_frees n1b) then
         begin
           match nexp_aux2 with
           | Nexp_times (n2a, n2b) when prove __POS__ env (NC_aux (NC_equal (n1b, n2b), Parse_ast.Unknown)) ->
              unify_nexp l env goals n1a n2a
           | Nexp_var kid when (not (KidSet.mem kid goals)) && valid nexp2 n1b && !opt_smt_div ->
              unify_nexp l env goals n1a (napp (mk_id "div") [nexp2; n1b])
           | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
         end
       else unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
    | Nexp_exp n1 ->
       begin
         match nexp_aux2 with
         | Nexp_exp n2 -> unify_nexp l env goals n1 n2
         | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)
       end
    | _ -> unify_error l ("Cannot unify Int expression " ^ string_of_nexp nexp1 ^ " with " ^ string_of_nexp nexp2)

let unify l env goals typ1 typ2 =
  typ_print (lazy (Util.("Unify " |> magenta |> clear) ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2
                   ^ " for " ^ Util.string_of_list ", " string_of_kid (KidSet.elements goals)));
  let typ1, typ2 = Env.expand_synonyms env typ1, Env.expand_synonyms env typ2 in
  if not (KidSet.is_empty (KidSet.inter goals (tyvars_of_typ typ2))) then
    typ_error env l ("Occurs check failed: " ^ string_of_typ typ2 ^ " contains "
                 ^ Util.string_of_list ", " string_of_kid (KidSet.elements goals))
  else
    unify_typ l env goals typ1 typ2

let subst_unifiers unifiers typ =
  List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ (KBindings.bindings unifiers)

let subst_unifiers_typ_arg unifiers typ_arg =
  List.fold_left (fun typ_arg (v, arg) -> typ_arg_subst v arg typ_arg) typ_arg (KBindings.bindings unifiers)

let instantiate_quant env (v, arg) (QI_aux (aux, l) as qi) =
  match aux with
  | QI_id kopt when Kid.compare (kopt_kid kopt) v = 0 ->
     typ_debug (lazy ("Instantiated " ^ string_of_quant_item qi));
     None
  | QI_id _ -> Some qi
  | QI_constant kopts ->
     let kopts =
       Util.map_filter (fun kopt ->
           if Kid.compare (kopt_kid kopt) v = 0 then
             begin match arg with
             | A_aux (A_nexp nexp, _) ->
                if is_nexp_constant (Env.expand_nexp_synonyms env nexp) then None else Some kopt
             | _ -> Some kopt
             end
           else
             Some kopt
         ) kopts in
     begin match kopts with
     | [] -> None
     | _ -> Some (QI_aux (QI_constant kopts, l))
     end
  | QI_constraint nc -> Some (QI_aux (QI_constraint (constraint_subst v arg nc), l))

let instantiate_quants env quants unifier =
  List.map (instantiate_quant env unifier) quants |> Util.option_these

(* During typechecking, we can run into the following issue, where we
   have a function like

   val and_bool : forall ('p : Bool) ('q : Bool). (bool('p), bool('q)) -> bool('p & 'q)

   and we want to check something like Q & P <= bool(X & Y)

   where Q => bool(Y) & P => bool(X)

   if we instantiate using the return type (which is usually good)
   we'll run into the situtation where we have to check bool(Y)
   subtype bool(X) because the quantifiers will get instantiated in
   the wrong order, despite the expression being otherwise well-typed
   the trick here is to recognise that we shouldn't unify on goals in
   certain ambiguous positions in types. In this case with and_bool,
   they'll be unambigiously unified with the argument types so it's
   better to just not bother with the return type.
*)
let rec ambiguous_vars' (Typ_aux (aux, _)) =
  match aux with
  | Typ_app (_, args) -> List.fold_left KidSet.union KidSet.empty (List.map ambiguous_arg_vars args)
  | _ -> KidSet.empty

and ambiguous_arg_vars (A_aux (aux, _)) =
  match aux with
  | A_bool nc -> ambiguous_nc_vars nc
  | A_nexp nexp -> ambiguous_nexp_vars nexp
  | _ -> KidSet.empty

and ambiguous_nc_vars (NC_aux (aux, _)) =
  match aux with
  | NC_and (nc1, nc2) -> KidSet.union (tyvars_of_constraint nc1) (tyvars_of_constraint nc2)
  | NC_bounded_le (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_lt (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_ge (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_bounded_gt (n1, n2) -> KidSet.union (tyvars_of_nexp n1) (tyvars_of_nexp n2)
  | NC_equal (n1, n2) | NC_not_equal (n1, n2) ->
     KidSet.union (ambiguous_nexp_vars n1) (ambiguous_nexp_vars n2)
  | _ -> KidSet.empty

and ambiguous_nexp_vars (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_sum (nexp1, nexp2) -> KidSet.union (tyvars_of_nexp nexp1) (tyvars_of_nexp nexp2)
  | _ -> KidSet.empty

let ambiguous_vars typ =
  let vars = ambiguous_vars' typ in
  if KidSet.cardinal vars > 1 then vars else KidSet.empty

(**************************************************************************)
(* 3.5. Subtyping with existentials                                       *)
(**************************************************************************)

let destruct_atom_nexp env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (f, [A_aux (A_nexp n, _)]), _)
       when string_of_id f = "atom" || string_of_id f = "implicit" -> Some n
  | Typ_aux (Typ_app (f, [A_aux (A_nexp n, _); A_aux (A_nexp m, _)]), _)
       when string_of_id f = "range" && nexp_identical n m -> Some n
  | _ -> None

let destruct_atom_kid env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (f, [A_aux (A_nexp (Nexp_aux (Nexp_var kid, _)), _)]), _)
       when string_of_id f = "atom" -> Some kid
  | Typ_aux (Typ_app (f, [A_aux (A_nexp (Nexp_aux (Nexp_var kid1, _)), _);
                          A_aux (A_nexp (Nexp_aux (Nexp_var kid2, _)), _)]), _)
       when string_of_id f = "range" && Kid.compare kid1 kid2 = 0 -> Some kid1
  | _ -> None

let destruct_atom_bool env typ =
  match Env.expand_synonyms env typ with
  | Typ_aux (Typ_app (f, [A_aux (A_bool nc, _)]), _) when string_of_id f = "atom_bool" ->
     Some nc
  | _ -> None

(* The kid_order function takes a set of Int-kinded kids, and returns
   a list of those kids in the order they appear in a type, as well as
   a set containing all the kids that did not occur in the type. We
   only care about Int-kinded kids because those are the only type
   that can appear in an existential. *)

let rec kid_order_nexp kind_map (Nexp_aux (aux, l) as nexp) =
  match aux with
  | Nexp_var kid when KBindings.mem kid kind_map ->
     ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | Nexp_var _ | Nexp_id _ | Nexp_constant _ -> ([], kind_map)
  | Nexp_exp nexp | Nexp_neg nexp -> kid_order_nexp kind_map nexp
  | Nexp_times (nexp1, nexp2) | Nexp_sum (nexp1, nexp2) | Nexp_minus (nexp1, nexp2) ->
     let (ord, kids) = kid_order_nexp kind_map nexp1 in
     let (ord', kids) = kid_order_nexp kids nexp2 in
     (ord @ ord', kids)
  | Nexp_app (id, nexps) ->
     List.fold_left (fun (ord, kids) nexp -> let (ord', kids) = kid_order_nexp kids nexp in (ord @ ord', kids)) ([], kind_map) nexps


let rec kid_order kind_map (Typ_aux (aux, l) as typ) =
  match aux with
  | Typ_var kid when KBindings.mem kid kind_map ->
     ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | Typ_id _ | Typ_var _ -> ([], kind_map)
  | Typ_tup typs ->
     List.fold_left (fun (ord, kids) typ -> let (ord', kids) = kid_order kids typ in (ord @ ord', kids)) ([], kind_map) typs
  | Typ_app (_, args) ->
     List.fold_left (fun (ord, kids) arg -> let (ord', kids) = kid_order_arg kids arg in (ord @ ord', kids)) ([], kind_map) args
  | Typ_fn _ | Typ_bidir _ | Typ_exist _ -> typ_error Env.empty l ("Existential or function type cannot appear within existential type: " ^ string_of_typ typ)
  | Typ_internal_unknown -> Reporting.unreachable l __POS__ "escaped Typ_internal_unknown"
and kid_order_arg kind_map (A_aux (aux, l) as arg) =
  match aux with
  | A_typ typ -> kid_order kind_map typ
  | A_nexp nexp -> kid_order_nexp kind_map nexp
  | A_bool nc -> kid_order_constraint kind_map nc
  | A_order _ -> ([], kind_map)
and kid_order_constraint kind_map (NC_aux (aux, l) as nc) =
  match aux with
  | NC_var kid | NC_set (kid, _) when KBindings.mem kid kind_map ->
     ([mk_kopt (unaux_kind (KBindings.find kid kind_map)) kid], KBindings.remove kid kind_map)
  | NC_var _ | NC_set _ -> ([], kind_map)
  | NC_true | NC_false -> ([], kind_map)
  | NC_equal (n1, n2) | NC_not_equal (n1, n2)
  | NC_bounded_le (n1, n2) | NC_bounded_ge (n1, n2)
  | NC_bounded_lt (n1, n2) | NC_bounded_gt (n1, n2) ->
     let ord1, kind_map = kid_order_nexp kind_map n1 in
     let ord2, kind_map = kid_order_nexp kind_map n2 in
     (ord1 @ ord2, kind_map)
  | NC_app (_, args) ->
     List.fold_left (fun (ord, kind_map) arg -> let  ord', kind_map = kid_order_arg kind_map arg in (ord @ ord', kind_map))
                    ([], kind_map) args
  | NC_and (nc1, nc2) | NC_or (nc1, nc2) ->
     let ord1, kind_map = kid_order_constraint kind_map nc1 in
     let ord2, kind_map = kid_order_constraint kind_map nc2 in
     (ord1 @ ord2, kind_map)

let rec alpha_equivalent env typ1 typ2 =
  let counter = ref 0 in
  let new_kid () = let kid = mk_kid ("alpha#" ^ string_of_int !counter) in (incr counter; kid) in

  let rec relabel (Typ_aux (aux, l) as typ) =
    let relabelled_aux =
      match aux with
      | Typ_internal_unknown -> Typ_internal_unknown
      | Typ_id _ | Typ_var _ -> aux
      | Typ_fn (arg_typs, ret_typ, eff) -> Typ_fn (List.map relabel arg_typs, relabel ret_typ, eff)
      | Typ_bidir (typ1, typ2, eff) -> Typ_bidir (relabel typ1, relabel typ2, eff)
      | Typ_tup typs -> Typ_tup (List.map relabel typs)
      | Typ_exist (kopts, nc, typ) ->
         let kind_map = List.fold_left (fun m kopt -> KBindings.add (kopt_kid kopt) (kopt_kind kopt) m) KBindings.empty kopts in
         let (kopts1, kind_map) = kid_order_constraint kind_map nc in
         let (kopts2, _) = kid_order kind_map typ in
         let kopts = kopts1 @ kopts2 in
         let kopts = List.map (fun kopt -> (kopt_kid kopt, mk_kopt (unaux_kind (kopt_kind kopt)) (new_kid ()))) kopts in
         let nc = List.fold_left (fun nc (kid, nk) -> constraint_subst kid (arg_kopt nk) nc) nc kopts in
         let typ = List.fold_left (fun nc (kid, nk) -> typ_subst kid (arg_kopt nk) nc) typ kopts in
         let kopts = List.map snd kopts in
         Typ_exist (kopts, nc, typ)
      | Typ_app (id, args) ->
         Typ_app (id, List.map relabel_arg args)
    in
    Typ_aux (relabelled_aux, l)
  and relabel_arg (A_aux (aux, l) as arg) =
    (* FIXME relabel constraint *)
    match aux with
    | A_nexp _ | A_order _ | A_bool _ -> arg
    | A_typ typ -> A_aux (A_typ (relabel typ), l)
  in

  let typ1 = relabel (Env.expand_synonyms env typ1) in
  counter := 0;
  let typ2 = relabel (Env.expand_synonyms env typ2) in
  typ_debug (lazy ("Alpha equivalence for " ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2));
  if typ_identical typ1 typ2
  then (typ_debug (lazy "alpha-equivalent"); true)
  else (typ_debug (lazy "Not alpha-equivalent"); false)

let unwrap_exist env typ =
  match destruct_exist (Env.expand_synonyms env typ) with
  | Some (kids, nc, typ) -> (kids, nc, typ)
  | None -> ([], nc_true, typ)

let unifier_constraint env (v, arg) =
  match arg with
  | A_aux (A_nexp nexp, _) -> Env.add_constraint (nc_eq (nvar v) nexp) env
  | _ -> env

let canonicalize env typ =
  let typ = Env.expand_synonyms env typ in
  let rec canon (Typ_aux (aux, l)) =
    match aux with
    | Typ_var v -> Typ_aux (Typ_var v, l)
    | Typ_internal_unknown -> Typ_aux (Typ_internal_unknown, l)
    | Typ_id id when string_of_id id = "int" ->
       exist_typ (fun _ -> nc_true) (fun v -> atom_typ (nvar v))
    | Typ_id id -> Typ_aux (Typ_id id, l)
    | Typ_app (id, [A_aux (A_nexp lo, _); A_aux (A_nexp hi, _)]) when string_of_id id = "range" ->
       exist_typ (fun v -> nc_and (nc_lteq lo (nvar v)) (nc_lteq (nvar v) hi)) (fun v -> atom_typ (nvar v))
    | Typ_app (id, args) ->
       Typ_aux (Typ_app (id, List.map canon_arg args), l)
    | Typ_tup typs ->
       let typs = List.map canon typs in
       let fold_exist (kids, nc, typs) typ =
         match destruct_exist typ with
         | Some (kids', nc', typ') -> (kids @ kids', nc_and nc nc', typs @ [typ'])
         | None -> (kids, nc, typs @ [typ])
       in
       let kids, nc, typs = List.fold_left fold_exist ([], nc_true, []) typs in
       if kids = [] then
         Typ_aux (Typ_tup typs, l)
       else
         Typ_aux (Typ_exist (kids, nc, Typ_aux (Typ_tup typs, l)), l)
    | Typ_exist (kids, nc, typ) ->
       begin match destruct_exist (canon typ) with
       | Some (kids', nc', typ') ->
          Typ_aux (Typ_exist (kids @ kids', nc_and nc nc', typ'), l)
       | None -> Typ_aux (Typ_exist (kids, nc, typ), l)
       end
    | Typ_fn _ | Typ_bidir _ -> raise (Reporting.err_unreachable l __POS__ "Function type passed to Type_check.canonicalize")
  and canon_arg (A_aux (aux, l)) =
    A_aux ((match aux with
            | A_typ typ -> A_typ (canon typ)
            | arg -> arg),
           l)
  in
  canon typ

let rec subtyp l env typ1 typ2 =
  let (Typ_aux (typ_aux1, _) as typ1) = Env.expand_synonyms env typ1 in
  let (Typ_aux (typ_aux2, _) as typ2) = Env.expand_synonyms env typ2 in
  typ_print (lazy (("Subtype " |> Util.green |> Util.clear) ^ string_of_typ typ1 ^ " and " ^ string_of_typ typ2));
  match destruct_numeric typ1, destruct_numeric typ2 with
  (* Ensure alpha equivalent types are always subtypes of one another
     - this ensures that we can always re-check inferred types. *)
  | _, _ when alpha_equivalent env typ1 typ2 -> ()
  (* Special cases for two numeric (atom) types *)
  | Some (kids1, nc1, nexp1), Some ([], _, nexp2) ->
     let env = add_existential l (List.map (mk_kopt K_int) kids1) nc1 env in
     if prove __POS__ env (nc_eq nexp1 nexp2) then () else typ_raise env l (Err_subtype (typ1, typ2, Env.get_constraints env, Env.get_typ_var_locs env))
  | Some (kids1, nc1, nexp1), Some (kids2, nc2, nexp2) ->
     let env = add_existential l (List.map (mk_kopt K_int) kids1) nc1 env in
     let env = add_typ_vars l (List.map (mk_kopt K_int) (KidSet.elements (KidSet.inter (nexp_frees nexp2) (KidSet.of_list kids2)))) env in
     let kids2 = KidSet.elements (KidSet.diff (KidSet.of_list kids2) (nexp_frees nexp2)) in
     if not (kids2 = []) then typ_error env l ("Universally quantified constraint generated: " ^ Util.string_of_list ", " string_of_kid kids2) else ();
     let vars = KBindings.filter (fun _ k -> match k with K_int | K_bool -> true | _ -> false) (Env.get_typ_vars env) in
     begin match Constraint.call_smt l (nc_eq nexp1 nexp2) with
     | Constraint.Sat ->
        let env = Env.add_constraint (nc_eq nexp1 nexp2) env in
        if prove __POS__ env nc2 then
          ()
        else
          typ_raise env l (Err_subtype (typ1, typ2, Env.get_constraints env, Env.get_typ_var_locs env))
     | _ ->
        typ_error env l ("Constraint " ^ string_of_n_constraint (nc_eq nexp1 nexp2) ^ " is not satisfiable")
     end
  | _, _ ->
  match typ_aux1, typ_aux2 with
  | _, Typ_internal_unknown when Env.allow_unknowns env -> ()

  | Typ_app (id1, _), Typ_id id2 when string_of_id id1 = "atom_bool" && string_of_id id2 = "bool" ->
     typ_debug (lazy "Boolean subtype");
     ()

  | Typ_tup typs1, Typ_tup typs2 when List.length typs1 = List.length typs2 ->
     List.iter2 (subtyp l env) typs1 typs2

  | Typ_app (id1, args1), Typ_app (id2, args2) when Id.compare id1 id2 = 0 && List.length args1 = List.length args2 ->
     List.iter2 (subtyp_arg l env) args1 args2

  | Typ_id id1, Typ_id id2 when Id.compare id1 id2 = 0 -> ()
  | Typ_id id1, Typ_app (id2, []) when Id.compare id1 id2 = 0 -> ()
  | Typ_app (id1, []), Typ_id id2 when Id.compare id1 id2 = 0 -> ()

  | _, _ ->
  match destruct_exist_plain typ1, destruct_exist (canonicalize env typ2) with
  | Some (kopts, nc, typ1), _ ->
     let env = add_existential l kopts nc env in subtyp l env typ1 typ2
  | None, Some (kopts, nc, typ2) ->
     typ_debug (lazy "Subtype check with unification");
     let typ1, env = bind_existential l None (canonicalize env typ1) env in
     let env = add_typ_vars l kopts env in
     let kids' = KidSet.elements (KidSet.diff (KidSet.of_list (List.map kopt_kid kopts)) (tyvars_of_typ typ2)) in
     if not (kids' = []) then typ_error env l "Universally quantified constraint generated" else ();
     let unifiers =
       try unify l env (KidSet.diff (tyvars_of_typ typ2) (tyvars_of_typ typ1)) typ2 typ1 with
       | Unification_error (_, m) -> typ_error env l m
     in
     let nc = List.fold_left (fun nc (kid, uvar) -> constraint_subst kid uvar nc) nc (KBindings.bindings unifiers) in
     let env = List.fold_left unifier_constraint env (KBindings.bindings unifiers) in
     if prove __POS__ env nc then ()
     else typ_raise env l (Err_subtype (typ1, typ2, Env.get_constraints env, Env.get_typ_var_locs env))
  | None, None -> typ_raise env l (Err_subtype (typ1, typ2, Env.get_constraints env, Env.get_typ_var_locs env))

and subtyp_arg l env (A_aux (aux1, _) as arg1) (A_aux (aux2, _) as arg2) =
  typ_print (lazy (("Subtype arg " |> Util.green |> Util.clear) ^ string_of_typ_arg arg1 ^ " and " ^ string_of_typ_arg arg2));
  match aux1, aux2 with
  | A_nexp n1, A_nexp n2 when prove __POS__ env (nc_eq n1 n2) -> ()
  | A_typ typ1, A_typ typ2 -> subtyp l env typ1 typ2
  | A_order ord1, A_order ord2 when ord_identical ord1 ord2 -> ()
  | A_bool nc1, A_bool nc2 when prove __POS__ env (nc_and (nc_or (nc_not nc1) nc2) (nc_or (nc_not nc2) nc1)) -> ()
  | _, _ -> typ_error env l "Mismatched argument types in sub-typing check"

let typ_equality l env typ1 typ2 =
  subtyp l env typ1 typ2; subtyp l env typ2 typ1

let subtype_check env typ1 typ2 =
  try subtyp Parse_ast.Unknown env typ1 typ2; true with
  | Type_error _ -> false

(**************************************************************************)
(* 4. Removing sizeof expressions                                         *)
(**************************************************************************)

exception No_simple_rewrite;;

let rec move_to_front p ys = function
  | x :: xs when p x -> x :: (ys @ xs)
  | x :: xs -> move_to_front p (x :: ys) xs
  | [] -> ys

let rec rewrite_sizeof' env (Nexp_aux (aux, l) as nexp) =
  let mk_exp exp = mk_exp ~loc:l exp in
  match aux with
  | Nexp_var v ->
     (* Use a simple heuristic to find the most likely local we can
        use, and move it to the front of the list. *)
     let str = string_of_kid v in
     let likely =
       try let n = if str.[1] = '_' then 2 else 1 in String.sub str n (String.length str - n) with
       | Invalid_argument _ -> str
     in
     let locals = Env.get_locals env |> Bindings.bindings in
     let locals = move_to_front (fun local -> likely = string_of_id (fst local)) [] locals in
     let same_size (local, (_, Typ_aux (aux, _))) =
       match aux with
       | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _)])
            when string_of_id id = "atom" && Kid.compare v v' = 0 -> true

       | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "atom" ->
          prove __POS__ env (nc_eq (nvar v) n)

       | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var v', _)), _); _]) when string_of_id id = "bitvector" ->
          Kid.compare v v' = 0

       | _ ->
          false
     in
     begin match List.find_opt same_size locals with
     | Some (id, (_, typ)) -> mk_exp (E_app (mk_id "__size", [mk_exp (E_id id)]))
     | None -> raise No_simple_rewrite
     end

  | Nexp_constant c ->
     mk_lit_exp (L_num c)

  | Nexp_neg nexp ->
     let exp = rewrite_sizeof' env nexp in
     mk_exp (E_app (mk_id "negate_atom", [exp]))

  | Nexp_sum (nexp1, nexp2) ->
     let exp1 = rewrite_sizeof' env nexp1 in
     let exp2 = rewrite_sizeof' env nexp2 in
     mk_exp (E_app (mk_id "add_atom", [exp1; exp2]))

  | Nexp_minus (nexp1, nexp2) ->
     let exp1 = rewrite_sizeof' env nexp1 in
     let exp2 = rewrite_sizeof' env nexp2 in
     mk_exp (E_app (mk_id "sub_atom", [exp1; exp2]))

  | Nexp_times (nexp1, nexp2) ->
     let exp1 = rewrite_sizeof' env nexp1 in
     let exp2 = rewrite_sizeof' env nexp2 in
     mk_exp (E_app (mk_id "mult_atom", [exp1; exp2]))

  | Nexp_exp nexp ->
     let exp = rewrite_sizeof' env nexp in
     mk_exp (E_app (mk_id "pow2", [exp]))

  (* SMT solver div/mod is euclidian, so we must use those versions of
     div and mod in lib/smt.sail *)
  | Nexp_app (id, [nexp1; nexp2]) when string_of_id id = "div" ->
     let exp1 = rewrite_sizeof' env nexp1 in
     let exp2 = rewrite_sizeof' env nexp2 in
     mk_exp (E_app (mk_id "ediv_int", [exp1; exp2]))

  | Nexp_app (id, [nexp1; nexp2]) when string_of_id id = "mod" ->
     let exp1 = rewrite_sizeof' env nexp1 in
     let exp2 = rewrite_sizeof' env nexp2 in
     mk_exp (E_app (mk_id "emod_int", [exp1; exp2]))

  | Nexp_app _ | Nexp_id _ ->
     typ_error env l ("Cannot re-write sizeof(" ^ string_of_nexp nexp ^ ")")

let rewrite_sizeof l env nexp =
  try rewrite_sizeof' env nexp with
  | No_simple_rewrite ->
     let locals = Env.get_locals env |> Bindings.bindings in
     let same_size (local, (_, Typ_aux (aux, _))) =
       match aux with
       | Typ_app (id, [A_aux (A_nexp n, _)]) when string_of_id id = "atom" ->
          prove __POS__ env (nc_eq nexp n)
       | _ -> false
     in
     begin match List.find_opt same_size locals with
     | Some (id, (_, typ)) -> mk_exp (E_app (mk_id "__size", [mk_exp (E_id id)]))
     | None -> typ_error env l ("Cannot re-write sizeof(" ^ string_of_nexp nexp ^ ")")
     end

let rec rewrite_nc env (NC_aux (nc_aux, l)) = mk_exp ~loc:l (rewrite_nc_aux l env nc_aux)
and rewrite_nc_aux l env =
  let mk_exp exp = mk_exp ~loc:l exp in
  function
  | NC_bounded_ge (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id ">=", mk_exp (E_sizeof n2))
  | NC_bounded_gt (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id ">", mk_exp (E_sizeof n2))
  | NC_bounded_le (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "<=", mk_exp (E_sizeof n2))
  | NC_bounded_lt (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "<", mk_exp (E_sizeof n2))
  | NC_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "==", mk_exp (E_sizeof n2))
  | NC_not_equal (n1, n2) -> E_app_infix (mk_exp (E_sizeof n1), mk_id "!=", mk_exp (E_sizeof n2))
  | NC_and (nc1, nc2) -> E_app_infix (rewrite_nc env nc1, mk_id "&", rewrite_nc env nc2)
  | NC_or (nc1, nc2) -> E_app_infix (rewrite_nc env nc1, mk_id "|", rewrite_nc env nc2)
  | NC_false -> E_lit (mk_lit L_false)
  | NC_true -> E_lit (mk_lit L_true)
  | NC_set (kid, []) -> E_lit (mk_lit (L_false))
  | NC_set (kid, int :: ints) ->
     let kid_eq kid int = nc_eq (nvar kid) (nconstant int) in
     unaux_exp (rewrite_nc env (List.fold_left (fun nc int -> nc_or nc (kid_eq kid int)) (kid_eq kid int) ints))
  | NC_app (f, [A_aux (A_bool nc, _)]) when string_of_id f = "not" ->
     E_app (mk_id "not_bool", [rewrite_nc env nc])
  | NC_app (f, args) ->
     unaux_exp (rewrite_nc env (Env.expand_constraint_synonyms env (mk_nc (NC_app (f, args)))))
  | NC_var v ->
     (* Would be better to translate change E_sizeof to take a kid, then rewrite to E_sizeof *)
     E_id (id_of_kid v)


(**************************************************************************)
(* 5. Type checking expressions                                           *)
(**************************************************************************)

(* The type checker produces a fully annoted AST - tannot is the type
   of these type annotations.  The extra typ option is the expected type,
   that is, the type that the AST node was checked against, if there was one. *)
type tannot' = {
    env : Env.t;
    typ : typ;
    effect : effect;
    expected : typ option;
    instantiation : typ_arg KBindings.t option
  }

type tannot = tannot' option

let mk_tannot env typ effect : tannot =
  Some {
      env = env;
      typ = Env.expand_synonyms env typ;
      effect = effect;
      expected = None;
      instantiation = None
    }

let mk_expected_tannot env typ effect expected : tannot =
  Some {
      env = env;
      typ = Env.expand_synonyms env typ;
      effect = effect;
      expected = expected;
      instantiation = None
    }

let get_instantiations = function
  | None -> None
  | Some t -> t.instantiation
  
let empty_tannot = None

let is_empty_tannot = function
  | None -> true
  | Some _ -> false

let destruct_tannot tannot = Util.option_map (fun t -> (t.env, t.typ, t.effect)) tannot

let string_of_tannot tannot =
  match destruct_tannot tannot with
  | Some (_, typ, eff) ->
     "Some (_, " ^ string_of_typ typ ^ ", " ^ string_of_effect eff ^ ")"
  | None -> "None"

let replace_typ typ = function
  | Some t -> Some { t with typ = typ }
  | None -> None

let replace_env env = function
  | Some t -> Some { t with env = env }
  | None -> None

(* Helpers for implicit arguments in infer_funapp' *)
let is_not_implicit (Typ_aux (aux, _)) =
  match aux with
  | Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var impl, _)), _)]) when string_of_id id = "implicit" -> false
  | _ -> true

let implicit_to_int (Typ_aux (aux, l)) =
  match aux with
  | Typ_app (id, args) when string_of_id id = "implicit" -> Typ_aux (Typ_app (mk_id "atom", args), l)
  | _ -> Typ_aux (aux, l)

let rec get_implicits typs =
  match typs with
  | Typ_aux (Typ_app (id, [A_aux (A_nexp (Nexp_aux (Nexp_var impl, _)), _)]), _) :: typs when string_of_id id = "implicit" ->
     impl :: get_implicits typs
  | _ :: typs -> get_implicits typs
  | [] -> []

let infer_lit env (L_aux (lit_aux, l) as lit) =
  match lit_aux with
  | L_unit -> unit_typ
  | L_zero -> bit_typ
  | L_one -> bit_typ
  | L_num n -> atom_typ (nconstant n)
  | L_true -> atom_bool_typ nc_true
  | L_false -> atom_bool_typ nc_false
  | L_string _ -> string_typ
  | L_real _ -> real_typ
  | L_bin str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) | Ord_aux (Ord_dec, _) ->
          bits_typ env (nint (String.length str))
       | Ord_aux (Ord_var _, _) -> typ_error env l default_order_error_string
     end
  | L_hex str ->
     begin
       match Env.get_default_order env with
       | Ord_aux (Ord_inc, _) | Ord_aux (Ord_dec, _) ->
          bits_typ env (nint (String.length str * 4))
       | Ord_aux (Ord_var _, _) -> typ_error env l default_order_error_string
     end
  | L_undef -> typ_error env l "Cannot infer the type of undefined"

let is_nat_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_order_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_order, _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let is_typ_kid kid = function
  | KOpt_aux (KOpt_kind (K_aux (K_type, _), kid'), _) -> Kid.compare kid kid' = 0
  | _ -> false

let instantiate_simple_equations =
  let rec find_eqs kid (NC_aux (nc,_)) = 
    match nc with
    | NC_equal (Nexp_aux (Nexp_var kid',_), nexp)
        when Kid.compare kid kid' == 0 &&
          not (KidSet.mem kid (nexp_frees nexp)) ->
       [arg_nexp nexp]
    | NC_and (nexp1, nexp2) ->
       find_eqs kid nexp1 @ find_eqs kid nexp2
    | _ -> []
  in
  let rec find_eqs_quant kid (QI_aux (qi,_)) =
    match qi with
    | QI_id _ | QI_constant _ -> []
    | QI_constraint nc -> find_eqs kid nc
  in
  let rec inst_from_eq = function
    | [] -> KBindings.empty
    | (QI_aux (QI_id kinded_kid, _) as quant) :: quants ->
       let kid = kopt_kid kinded_kid in
       let insts_tl = inst_from_eq quants in
       begin
         match List.concat (List.map (find_eqs_quant kid) quants) with
         | [] -> insts_tl
         | h::_ -> KBindings.add kid h (KBindings.map (typ_arg_subst kid h) insts_tl)
       end
    | quant :: quants ->
       inst_from_eq quants
in inst_from_eq

type destructed_vector =
  | Destruct_vector of nexp * order * typ
  | Destruct_bitvector of nexp * order

let destruct_any_vector_typ l env typ =
  let destruct_any_vector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _)]
                       ), _) when string_of_id id = "bitvector" -> Destruct_bitvector (n1, o)
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _);
                             A_aux (A_typ vtyp, _)]
                       ), _) when string_of_id id = "vector" -> Destruct_vector (n1, o, vtyp)
    | typ -> typ_error env l ("Expected vector or bitvector type, got " ^ string_of_typ typ)
  in
  destruct_any_vector_typ' l (Env.expand_synonyms env typ)

let destruct_vector_typ l env typ =
  let destruct_vector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _);
                             A_aux (A_typ vtyp, _)]
                       ), _) when string_of_id id = "vector" -> n1, o, vtyp
    | typ -> typ_error env l ("Expected vector type, got " ^ string_of_typ typ)
  in
  destruct_vector_typ' l (Env.expand_synonyms env typ)

let destruct_bitvector_typ l env typ =
  let destruct_bitvector_typ' l = function
    | Typ_aux (Typ_app (id, [A_aux (A_nexp n1, _);
                             A_aux (A_order o, _)]
                       ), _) when string_of_id id = "bitvector" -> n1, o
    | typ -> typ_error env l ("Expected bitvector type, got " ^ string_of_typ typ)
  in
  destruct_bitvector_typ' l (Env.expand_synonyms env typ)

let env_of_annot (l, tannot) = match tannot with
  | Some t -> t.env
  | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

let env_of_tannot tannot = match tannot with
  | Some t -> t.env
  | None -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "no type annotation")

let typ_of_tannot tannot = match tannot with
  | Some t -> t.typ
  | None -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "no type annotation")

let env_of (E_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_annot (l, tannot) = match tannot with
  | Some t -> t.typ
  | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

let typ_of (E_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of (E_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_pat (P_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_pat (P_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_pexp (Pat_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_pexp (Pat_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_mpat (MP_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_mpat (MP_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let typ_of_mpexp (MPat_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let env_of_mpexp (MPat_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let lexp_typ_of (LEXP_aux (_, (l, tannot))) = typ_of_annot (l, tannot)

let lexp_env_of (LEXP_aux (_, (l, tannot))) = env_of_annot (l, tannot)

let expected_typ_of (l, tannot) = match tannot with
  | Some t -> t.expected
  | None -> raise (Reporting.err_unreachable l __POS__ "no type annotation")

(* Flow typing *)

type simple_numeric =
  | Equal of nexp
  | Constraint of (kid -> n_constraint)
  | Anything

let to_simple_numeric l kids nc (Nexp_aux (aux, _) as n) =
  match aux, kids with
  | Nexp_var v, [v'] when Kid.compare v v' = 0 ->
     Constraint (fun subst -> constraint_subst v (arg_nexp (nvar subst)) nc)
  | _, [] ->
     Equal n
  | _ ->
     typ_error Env.empty l "Numeric type is non-simple"

let union_simple_numeric ex1 ex2 =
  match ex1, ex2 with
  | Equal nexp1, Equal nexp2 ->
     Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp1) (nc_eq (nvar kid) nexp2))

  | Equal nexp, Constraint c ->
     Constraint (fun kid -> nc_or (nc_eq (nvar kid) nexp) (c kid))

  | Constraint c, Equal nexp ->
     Constraint (fun kid -> nc_or (c kid) (nc_eq (nvar kid) nexp))

  | _, _ -> Anything

let typ_of_simple_numeric = function
  | Anything -> int_typ
  | Equal nexp -> atom_typ nexp
  | Constraint c -> exist_typ c (fun kid -> atom_typ (nvar kid))

let rec big_int_of_nexp (Nexp_aux (nexp, _)) = match nexp with
  | Nexp_constant c -> Some c
  | Nexp_times (n1, n2) ->
     Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_sum (n1, n2) ->
     Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_minus (n1, n2) ->
     Util.option_binop Big_int.add (big_int_of_nexp n1) (big_int_of_nexp n2)
  | Nexp_exp n ->
     Util.option_map (fun n -> Big_int.pow_int_positive 2 (Big_int.to_int n)) (big_int_of_nexp n)
  | _ -> None

let destruct_atom (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_app (f, [A_aux (A_nexp nexp, _)])
       when string_of_id f = "atom" ->
     Util.option_map (fun c -> (c, nexp)) (big_int_of_nexp nexp)
  | Typ_app (f, [A_aux (A_nexp nexp1, _); A_aux (A_nexp nexp2, _)])
       when string_of_id f = "range" ->
     begin
       match big_int_of_nexp nexp1, big_int_of_nexp nexp2 with
       | Some c1, Some c2 -> if Big_int.equal c1 c2 then Some (c1, nexp1) else None
       | _ -> None
     end
  | _ -> None

exception Not_a_constraint;;

let rec assert_nexp env exp = destruct_atom_nexp env (typ_of exp)

let rec combine_constraint b f x y = match b, x, y with
  | true,  Some x, Some y -> Some (f x y)
  | true,  Some x, None   -> Some x
  | true,  None,   Some y -> Some y
  | false, Some x, Some y -> Some (f x y)
  | _, _, _ -> None

let rec assert_constraint env b (E_aux (exp_aux, _) as exp) =
  typ_debug ~level:2 (lazy ("Asserting constraint for " ^ string_of_exp exp ^ " : " ^ string_of_typ (typ_of exp)));
  match typ_of exp with
  | Typ_aux (Typ_app (Id_aux (Id "atom_bool", _), [A_aux (A_bool nc, _)]), _) ->
     Some nc
  | _ ->
  match exp_aux with
  | E_constraint nc ->
     Some nc
  | E_lit (L_aux (L_true, _)) -> Some nc_true
  | E_lit (L_aux (L_false, _)) -> Some nc_false
  | E_let (_,e) ->
     assert_constraint env b e (* TODO: beware of fresh type vars *)
  | E_app (op, [x; y]) when string_of_id op = "or_bool" ->
     combine_constraint (not b) nc_or (assert_constraint env b x) (assert_constraint env b y)
  | E_app (op, [x; y]) when string_of_id op = "and_bool" ->
     combine_constraint b nc_and (assert_constraint env b x) (assert_constraint env b y)
  | E_app (op, [x; y]) when string_of_id op = "gteq_int" ->
     option_binop nc_gteq (assert_nexp env x) (assert_nexp env y)
  | E_app (op, [x; y]) when string_of_id op = "lteq_int" ->
     option_binop nc_lteq (assert_nexp env x) (assert_nexp env y)
  | E_app (op, [x; y]) when string_of_id op = "gt_int" ->
     option_binop nc_gt (assert_nexp env x) (assert_nexp env y)
  | E_app (op, [x; y]) when string_of_id op = "lt_int" ->
     option_binop nc_lt (assert_nexp env x) (assert_nexp env y)
  | E_app (op, [x; y]) when string_of_id op = "eq_int" ->
     option_binop nc_eq (assert_nexp env x) (assert_nexp env y)
  | E_app (op, [x; y]) when string_of_id op = "neq_int" ->
     option_binop nc_neq (assert_nexp env x) (assert_nexp env y)
  | _ ->
     None

let rec add_opt_constraint constr env =
  match constr with
  | None -> env
  | Some constr -> Env.add_constraint constr env

let rec add_constraints constrs env =
  List.fold_left (fun env constr -> Env.add_constraint constr env) env constrs

let solve_quant env = function
  | QI_aux (QI_id _, _) -> false
  | QI_aux (QI_constant _, _) -> false
  | QI_aux (QI_constraint nc, _) -> prove __POS__ env nc

(* When doing implicit type coercion, for performance reasons we want
   to filter out the possible casts to only those that could
   reasonably apply. We don't mind if we try some coercions that are
   impossible, but we should be careful to never rule out a possible
   cast - match_typ and filter_casts implement this logic. It must be
   the case that if two types unify, then they match. *)
let rec match_typ env typ1 typ2 =
  let Typ_aux (typ1_aux, _) = Env.expand_synonyms env typ1 in
  let Typ_aux (typ2_aux, _) = Env.expand_synonyms env typ2 in
  match typ1_aux, typ2_aux with
  | Typ_exist (_, _, typ1), _ -> match_typ env typ1 typ2
  | _, Typ_exist (_, _, typ2) -> match_typ env typ1 typ2
  | _, Typ_var kid2 -> true
  | Typ_id v1, Typ_id v2 when Id.compare v1 v2 = 0 -> true
  | Typ_id v1, Typ_id v2 when string_of_id v1 = "int" && string_of_id v2 = "nat" -> true
  | Typ_tup typs1, Typ_tup typs2 -> List.for_all2 (match_typ env) typs1 typs2
  | Typ_id v, Typ_app (f, _) when string_of_id v = "nat" && string_of_id f = "atom" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "int" &&  string_of_id f = "atom" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "nat" &&  string_of_id f = "range" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "int" &&  string_of_id f = "range" -> true
  | Typ_id v, Typ_app (f, _) when string_of_id v = "bool" &&  string_of_id f = "atom_bool" -> true
  | Typ_app (f, _), Typ_id v when string_of_id v = "bool" &&  string_of_id f = "atom_bool" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when string_of_id f1 = "range" && string_of_id f2 = "atom" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when string_of_id f1 = "atom" && string_of_id f2 = "range" -> true
  | Typ_app (f1, _), Typ_app (f2, _) when Id.compare f1 f2 = 0 -> true
  | Typ_id v1, Typ_app (f2, _) when Id.compare v1 f2 = 0 -> true
  | Typ_app (f1, _), Typ_id v2 when Id.compare f1 v2 = 0 -> true
  | _, _ -> false

let rec filter_casts env from_typ to_typ casts =
  match casts with
  | (cast :: casts) ->
     begin
       let (quant, cast_typ) = Env.get_val_spec cast env in
       match cast_typ with
       (* A cast should be a function A -> B and have only a single argument type. *)
       | Typ_aux (Typ_fn (arg_typs, cast_to_typ, _), _) ->
          begin match List.filter is_not_implicit arg_typs with
          | [cast_from_typ] when match_typ env from_typ cast_from_typ && match_typ env to_typ cast_to_typ ->
             typ_print (lazy ("Considering cast " ^ string_of_typ cast_typ
                              ^ " for " ^ string_of_typ from_typ ^ " to " ^ string_of_typ to_typ));
             cast :: filter_casts env from_typ to_typ casts
          | _ -> filter_casts env from_typ to_typ casts
          end
       | _ -> filter_casts env from_typ to_typ casts
     end
  | [] -> []

type pattern_duplicate =
  | Pattern_singleton of l
  | Pattern_duplicate of l * l 

let is_enum_member id env = match Env.lookup_id id env with
  | Enum _ -> true
  | _ -> false
                       
(* Check if a pattern contains duplicate bindings, and raise a type
   error if this is the case *)
let check_pattern_duplicates env pat =
  let is_duplicate _ = function
    | Pattern_duplicate _ -> true
    | _ -> false
  in
  let rec collect_duplicates ids (P_aux (aux, (l, _))) =
    let update_id = function
      | None -> Some (Pattern_singleton l)
      | Some (Pattern_singleton l2) -> Some (Pattern_duplicate (l2, l))
      | duplicate -> duplicate
    in
    match aux with
    | P_id id when not (is_enum_member id env) ->
       ids := Bindings.update id update_id !ids
    | P_id _ | P_lit _ | P_wild -> ()
    | P_not p | P_as (p, _) | P_typ (_, p) | P_var (p, _) ->
       collect_duplicates ids p
    | P_or (p1, p2) | P_cons (p1, p2) ->
       collect_duplicates ids p1; collect_duplicates ids p2
    | P_app (_, ps) | P_vector ps | P_vector_concat ps | P_tup ps | P_list ps | P_string_append ps ->
       List.iter (collect_duplicates ids) ps
  in
  let ids = ref Bindings.empty in
  collect_duplicates ids pat;
  match Bindings.choose_opt (Bindings.filter is_duplicate !ids) with
  | Some (id, Pattern_duplicate (l1, l2)) ->
     typ_raise env l2
       (Err_because (Err_other ("Duplicate binding for " ^ string_of_id id ^ " in pattern"),
                     l1,
                     Err_other ("Previous binding of " ^ string_of_id id ^ " here")))
  | _ -> ()
 
let crule r env exp typ =
  incr depth;
  typ_print (lazy (Util.("Check " |> cyan |> clear) ^ string_of_exp exp ^ " <= " ^ string_of_typ typ));
  try
    let checked_exp = r env exp typ in
    Env.wf_typ env (typ_of checked_exp);
    decr depth; checked_exp
  with
  | Type_error (env, l, err) -> decr depth; typ_raise env l err

let irule r env exp =
  incr depth;
  try
    let inferred_exp = r env exp in
    typ_print (lazy (Util.("Infer " |> blue |> clear) ^ string_of_exp exp ^ " => " ^ string_of_typ (typ_of inferred_exp)));
    Env.wf_typ env (typ_of inferred_exp);
    decr depth;
    inferred_exp
  with
  | Type_error (env, l, err) -> decr depth; typ_raise env l err


(* This function adds useful assertion messages to asserts missing them *)
let assert_msg = function
  | E_aux (E_lit (L_aux (L_string "", _)), (l, _)) ->
     let open Reporting in
     locate (fun _ -> l) (mk_lit_exp (L_string (short_loc_to_string l)))
  | msg -> msg

let strip_exp : 'a exp -> unit exp = function exp -> map_exp_annot (fun (l, _) -> (l, ())) exp
let strip_pat : 'a pat -> unit pat = function pat -> map_pat_annot (fun (l, _) -> (l, ())) pat
let strip_pexp : 'a pexp -> unit pexp = function pexp -> map_pexp_annot (fun (l, _) -> (l, ())) pexp
let strip_lexp : 'a lexp -> unit lexp = function lexp -> map_lexp_annot (fun (l, _) -> (l, ())) lexp

let strip_mpat : 'a. 'a mpat -> unit mpat = function mpat -> map_mpat_annot (fun (l, _) -> (l, ())) mpat
let strip_mpexp : 'a. 'a mpexp -> unit mpexp = function mpexp -> map_mpexp_annot (fun (l, _) -> (l, ())) mpexp
let strip_mapcl : 'a. 'a mapcl -> unit mapcl = function mapcl -> map_mapcl_annot (fun (l, _) -> (l, ())) mapcl

let fresh_var =
  let counter = ref 0 in
  fun () -> let n = !counter in
            let () = counter := n+1 in
            mk_id ("v#" ^ string_of_int n)

let rec exp_unconditionally_returns (E_aux (aux, _)) =
  match aux with
  | E_return _ -> true
  | E_block [] -> false
  | E_block exps -> exp_unconditionally_returns (List.hd (List.rev exps))
  | _ -> false

module PC_config = struct
  type t = tannot
  let typ_of_pat = typ_of_pat
end

module PC = Pattern_completeness.Make(PC_config);;
       
let rec check_exp env (E_aux (exp_aux, (l, ())) as exp : unit exp) (Typ_aux (typ_aux, _) as typ) : tannot exp =
  let annot_exp_effect exp typ' eff = E_aux (exp, (l, mk_expected_tannot env typ' eff (Some typ))) in
  let add_effect exp eff = match exp with
    | E_aux (exp, (l, Some tannot)) -> E_aux (exp, (l, Some { tannot with effect = eff }))
    | _ -> failwith "Tried to add effect to unannoted expression"
  in
  let annot_exp exp typ = annot_exp_effect exp typ no_effect in
  match (exp_aux, typ_aux) with
  | E_block exps, _ ->
     annot_exp (E_block (check_block l env exps (Some typ))) typ
  | E_case (exp, cases), _ ->
     let inferred_exp = irule infer_exp env exp in
     let inferred_typ = typ_of inferred_exp in
     let checked_cases = List.map (fun case -> check_case env inferred_typ case typ) cases in
     if !opt_check_completeness then (
       let ctx = {
           Pattern_completeness.variants = Env.get_variants env;
           Pattern_completeness.enums = Env.get_enums env
         } in
       ignore (PC.is_complete l ctx checked_cases inferred_typ)
     );
     annot_exp (E_case (inferred_exp, checked_cases)) typ
  | E_try (exp, cases), _ ->
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_try (checked_exp, List.map (fun case -> check_case env exc_typ case typ) cases)) typ
  | E_cons (x, xs), _ ->
     begin
       match is_list (Env.expand_synonyms env typ) with
       | Some elem_typ ->
          let checked_xs = crule check_exp env xs typ in
          let checked_x = crule check_exp env x elem_typ in
          annot_exp (E_cons (checked_x, checked_xs)) typ
       | None -> typ_error env l ("Cons " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
     end
  | E_list xs, _ ->
     begin
       match is_list (Env.expand_synonyms env typ) with
       | Some elem_typ ->
          let checked_xs = List.map (fun x -> crule check_exp env x elem_typ) xs in
          annot_exp (E_list checked_xs) typ
       | None -> typ_error env l ("List " ^ string_of_exp exp ^ " must have list type, got " ^ string_of_typ typ)
     end
  | E_record_update (exp, fexps), _ ->
     let checked_exp = crule check_exp env exp typ in
     let rectyp_id = match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
          rectyp_id
       | _ -> typ_error env l ("The type " ^ string_of_typ typ ^ " is not a record")
     in
     let check_fexp (FE_aux (FE_Fexp (field, exp), (l, ()))) =
       let (typq, rectyp_q, field_typ, _) = Env.get_accessor rectyp_id field env in
       let unifiers = try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ with Unification_error (l, m) -> typ_error env l ("Unification error: " ^ m) in
       let field_typ' = subst_unifiers unifiers field_typ in
       let checked_exp = crule check_exp env exp field_typ' in
       FE_aux (FE_Fexp (field, checked_exp), (l, None))
     in
     annot_exp (E_record_update (checked_exp, List.map check_fexp fexps)) typ
  | E_record fexps, _ ->
     let rectyp_id = match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
          rectyp_id
       | _ -> typ_error env l ("The type " ^ string_of_typ typ ^ " is not a record")
     in
     let record_fields = ref (Env.get_record rectyp_id env |> snd |> List.map snd |> IdSet.of_list) in
     let check_fexp (FE_aux (FE_Fexp (field, exp), (l, ()))) =
       record_fields := IdSet.remove field !record_fields;
       let (typq, rectyp_q, field_typ, _) = Env.get_accessor rectyp_id field env in
       let unifiers = try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ with Unification_error (l, m) -> typ_error env l ("Unification error: " ^ m) in
       let field_typ' = subst_unifiers unifiers field_typ in
       let checked_exp = crule check_exp env exp field_typ' in
       FE_aux (FE_Fexp (field, checked_exp), (l, None))
     in
     let fexps = List.map check_fexp fexps in
     if IdSet.is_empty !record_fields then
       annot_exp (E_record fexps) typ
     else
       typ_error env l ("struct literal missing fields: " ^ string_of_list ", " string_of_id (IdSet.elements !record_fields))
  | E_let (LB_aux (letbind, (let_loc, _)), exp), _ ->
     begin
       match letbind with
       | LB_val (P_aux (P_typ (ptyp, _), _) as pat, bind) ->
          Env.wf_typ env ptyp;
          let checked_bind = crule check_exp env bind ptyp in
          check_pattern_duplicates env pat;
          let tpat, inner_env = bind_pat_no_guard env pat ptyp in
          annot_exp (E_let (LB_aux (LB_val (tpat, checked_bind), (let_loc, None)), crule check_exp inner_env exp typ))
            (check_shadow_leaks l inner_env env typ)
       | LB_val (pat, bind) ->
          let inferred_bind = irule infer_exp env bind in
          check_pattern_duplicates env pat;
          let tpat, inner_env = bind_pat_no_guard env pat (typ_of inferred_bind) in
          annot_exp (E_let (LB_aux (LB_val (tpat, inferred_bind), (let_loc, None)), crule check_exp inner_env exp typ))
            (check_shadow_leaks l inner_env env typ)
     end
  | E_app_infix (x, op, y), _ ->
     check_exp env (E_aux (E_app (deinfix op, [x; y]), (l, ()))) typ
  | E_app (f, [E_aux (E_constraint nc, _)]), _ when string_of_id f = "_prove" ->
     Env.wf_constraint env nc;
     if prove __POS__ env nc
     then annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
     else typ_error env l ("Cannot prove " ^ string_of_n_constraint nc)
  | E_app (f, [E_aux (E_constraint nc, _)]), _ when string_of_id f = "_not_prove" ->
     Env.wf_constraint env nc;
     if prove __POS__ env nc
     then typ_error env l ("Can prove " ^ string_of_n_constraint nc)
     else annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
  | E_app (f, [E_aux (E_cast (typ, exp), _)]), _ when string_of_id f = "_check" ->
     Env.wf_typ env typ;
     let _ = crule check_exp env exp typ in
     annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
  | E_app (f, [E_aux (E_cast (typ, exp), _)]), _ when string_of_id f = "_not_check" ->
     Env.wf_typ env typ;
     if (try (ignore (crule check_exp env exp typ); false) with Type_error _ -> true)
     then annot_exp (E_lit (L_aux (L_unit, Parse_ast.Unknown))) unit_typ
     else typ_error env l (Printf.sprintf "Expected _not_check(%s : %s) to fail" (string_of_exp exp) (string_of_typ typ))
  (* All constructors and mappings are treated as having one argument
     so Ctor(x, y) is checked as Ctor((x, y)) *)
  | E_app (f, x :: y :: zs), _ when Env.is_union_constructor f env || Env.is_mapping f env ->
     typ_print (lazy ("Checking multiple argument constructor or mapping: " ^ string_of_id f));
     crule check_exp env (mk_exp ~loc:l (E_app (f, [mk_exp ~loc:l (E_tuple (x :: y :: zs))]))) typ
  | E_app (mapping, xs), _ when Env.is_mapping mapping env ->
     let forwards_id = mk_id (string_of_id mapping ^ "_forwards") in
     let backwards_id = mk_id (string_of_id mapping ^ "_backwards") in
     typ_print (lazy("Trying forwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
     begin try crule check_exp env (E_aux (E_app (forwards_id, xs), (l, ()))) typ with
           | Type_error (_, _, err1) ->
              (* typ_print (lazy ("Error in forwards direction: " ^ string_of_type_error err1)); *)
              typ_print (lazy ("Trying backwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
              begin try crule check_exp env (E_aux (E_app (backwards_id, xs), (l, ()))) typ with
                    | Type_error (_, _, err2) ->
                       (* typ_print (lazy ("Error in backwards direction: " ^ string_of_type_error err2)); *)
                       typ_raise env l (Err_no_overloading (mapping, [(forwards_id, err1); (backwards_id, err2)]))
              end
     end
  | E_app (f, xs), _ when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload = function
       | (errs, []) -> typ_raise env l (Err_no_overloading (f, errs))
       | (errs, (f :: fs)) -> begin
           typ_print (lazy ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
           try crule check_exp env (E_aux (E_app (f, xs), (l, ()))) typ with
           | Type_error (_, _, err) ->
              typ_debug (lazy "Error");
              try_overload (errs @ [(f, err)], fs)
         end
     in
     try_overload ([], Env.get_overloads f env)
  | E_app (f, [x; y]), _ when string_of_id f = "and_bool" || string_of_id f = "or_bool" ->
     (* We have to ensure that the type of y in (x || y) and (x && y)
        is non-empty, otherwise it could force the entire type of the
        expression to become empty even when unevaluted due to
        short-circuiting. *)
     begin match destruct_exist (typ_of (irule infer_exp env y)) with
     | None | Some (_, NC_aux (NC_true, _), _) ->
        let inferred_exp = infer_funapp l env f [x; y] (Some typ) in
        type_coercion env inferred_exp typ
     | Some _ ->
        let inferred_exp = infer_funapp l env f [x; mk_exp (E_cast (bool_typ, y))] (Some typ) in
        type_coercion env inferred_exp typ
     | exception Type_error _ ->
        let inferred_exp = infer_funapp l env f [x; mk_exp (E_cast (bool_typ, y))] (Some typ) in
        type_coercion env inferred_exp typ
     end
  | E_app (f, xs), _ ->
     let inferred_exp = infer_funapp l env f xs (Some typ) in
     type_coercion env inferred_exp typ
  | E_return exp, _ ->
     let checked_exp = match Env.get_ret_typ env with
       | Some ret_typ -> crule check_exp env exp ret_typ
       | None -> typ_error env l "Cannot use return outside a function"
     in
     annot_exp (E_return checked_exp) typ
  | E_tuple exps, Typ_tup typs when List.length exps = List.length typs ->
     let checked_exps = List.map2 (fun exp typ -> crule check_exp env exp typ) exps typs in
     annot_exp (E_tuple checked_exps) typ
  | E_if (cond, then_branch, else_branch), _ ->
     let cond' = try irule infer_exp env cond with Type_error _ -> crule check_exp env cond bool_typ in
     begin match destruct_exist (typ_of cond') with
     | Some (kopts, nc, Typ_aux (Typ_app (ab, [A_aux (A_bool flow, _)]), _)) when string_of_id ab = "atom_bool" ->
        let env = add_existential l kopts nc env in
        let then_branch' = crule check_exp (Env.add_constraint flow env) then_branch typ in
        let else_branch' = crule check_exp (Env.add_constraint (nc_not flow) env) else_branch typ in
        annot_exp (E_if (cond', then_branch', else_branch')) typ
     | _ ->
        let cond' = type_coercion env cond' bool_typ in
        let then_branch' = crule check_exp (add_opt_constraint (assert_constraint env true cond') env) then_branch typ in
        let else_branch' = crule check_exp (add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env) else_branch typ in
        annot_exp (E_if (cond', then_branch', else_branch')) typ
     end
  | E_exit exp, _ ->
     let checked_exp = crule check_exp env exp unit_typ in
     annot_exp_effect (E_exit checked_exp) typ (mk_effect [BE_escape])
  | E_throw exp, _ ->
     let checked_exp = crule check_exp env exp exc_typ in
     annot_exp_effect (E_throw checked_exp) typ (mk_effect [BE_escape])
  | E_var (lexp, bind, exp), _ ->
     let lexp, bind, env = match bind_assignment l env lexp bind with
       | E_aux (E_assign (lexp, bind), _), env -> lexp, bind, env
       | _, _ -> assert false
     in
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_var (lexp, bind, checked_exp)) typ
  | E_internal_return exp, _ ->
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_internal_return checked_exp) typ
  | E_internal_plet (pat, bind, body), _ ->
     let bind_exp, ptyp = match pat with
       | P_aux (P_typ (ptyp, _), _) ->
          Env.wf_typ env ptyp;
          let checked_bind = crule check_exp env bind ptyp in
          checked_bind, ptyp
       | _ ->
          let inferred_bind = irule infer_exp env bind in
          inferred_bind, typ_of inferred_bind in
     let tpat, env = bind_pat_no_guard env pat ptyp in
     (* Propagate constraint assertions on the lhs of monadic binds to the rhs *)
     let env = match bind_exp with
       | E_aux (E_assert (constr_exp, _), _) ->
          begin
            match assert_constraint env true constr_exp with
            | Some nc ->
               typ_print (lazy ("Adding constraint " ^ string_of_n_constraint nc ^ " for assert"));
               Env.add_constraint nc env
            | None -> env
          end
       | E_aux (E_if (cond, e_t, e_e), _) ->
          begin
            match unaux_exp (fst (uncast_exp e_t)) with
            | E_throw _ | E_block [E_aux (E_throw _, _)] ->
               add_opt_constraint (option_map nc_not (assert_constraint env false cond)) env
            | _ -> env
          end
       | _ -> env in
     let checked_body = crule check_exp env body typ in
     annot_exp (E_internal_plet (tpat, bind_exp, checked_body)) typ
  | E_vector vec, _ ->
     let len, ord, vtyp = match destruct_any_vector_typ l env typ with
       | Destruct_vector (len, ord, vtyp) -> len, ord, vtyp
       | Destruct_bitvector (len, ord) -> len, ord, bit_typ
     in
     let checked_items = List.map (fun i -> crule check_exp env i vtyp) vec in
     if prove __POS__ env (nc_eq (nint (List.length vec)) (nexp_simp len)) then annot_exp (E_vector checked_items) typ
     else typ_error env l "List length didn't match" (* FIXME: improve error message *)
  | E_lit (L_aux (L_undef, _) as lit), _ ->
     if is_typ_monomorphic typ || Env.polymorphic_undefineds env
     then annot_exp_effect (E_lit lit) typ (mk_effect [BE_undef])
     else typ_error env l ("Type " ^ string_of_typ typ ^ " failed undefined monomorphism restriction")
  | _, _ ->
     let inferred_exp = irule infer_exp env exp in
     type_coercion env inferred_exp typ

and check_block l env exps ret_typ =
  let final env exp = match ret_typ with
    | Some typ -> crule check_exp env exp typ
    | None -> irule infer_exp env exp
  in
  let annot_exp_effect exp typ eff exp_typ = E_aux (exp, (l, mk_expected_tannot env typ eff exp_typ)) in
  let annot_exp exp typ exp_typ = annot_exp_effect exp typ no_effect exp_typ in
  match Nl_flow.analyze exps with
  | [] -> (match ret_typ with Some typ -> typ_equality l env typ unit_typ; [] | None -> [])
  | [exp] -> [final env exp]
  | (E_aux (E_assign (lexp, bind), (assign_l, _)) :: exps) ->
     let texp, env = bind_assignment assign_l env lexp bind in
     texp :: check_block l env exps ret_typ
  | ((E_aux (E_assert (constr_exp, msg), (assert_l, _)) as exp) :: exps) ->
     let msg = assert_msg msg in
     let constr_exp = crule check_exp env constr_exp bool_typ in
     let checked_msg = crule check_exp env msg string_typ in
     let env, added_constraint = match assert_constraint env true constr_exp with
       | Some nc ->
          typ_print (lazy (adding ^ "constraint " ^ string_of_n_constraint nc ^ " for assert"));
          Env.add_constraint nc env, true
       | None -> env, false
     in
     let texp = annot_exp_effect (E_assert (constr_exp, checked_msg)) unit_typ (mk_effect [BE_escape]) (Some unit_typ) in
     let checked_exps = check_block l env exps ret_typ in
     (* If we can prove false, then any code after the assertion is
        dead. In this inconsistent typing environment we can do some
        broken things, so we eliminate this dead code here *)
     if added_constraint && List.compare_length_with exps 1 >= 0 && prove __POS__ env nc_false then (
       let ret_typ = List.rev checked_exps |> List.hd |> typ_of in
       texp :: [crule check_exp env (mk_exp ~loc:assert_l (E_exit (mk_lit_exp L_unit))) ret_typ]
     ) else (
       texp :: checked_exps
     )
  | ((E_aux (E_if (cond, (E_aux (E_throw _, _) | E_aux (E_block [E_aux (E_throw _, _)], _)), _), _) as exp) :: exps) ->
     let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let env = add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env in
     texp :: check_block l env exps ret_typ
  | ((E_aux (E_if (cond, true_exp, _), _) as exp) :: exps) when exp_unconditionally_returns true_exp ->
     let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let env = add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env in
     texp :: check_block l env exps ret_typ
  | (exp :: exps) ->
     let texp = crule check_exp env exp (mk_typ (Typ_id (mk_id "unit"))) in
     texp :: check_block l env exps ret_typ

and check_case env pat_typ pexp typ =
  let pat,guard,case,((l,_) as annot) = destruct_pexp pexp in
  check_pattern_duplicates env pat;
  match bind_pat env pat pat_typ with
  | tpat, env, guards ->
     let guard = match guard, guards with
       | None, h::t -> Some (h,t)
       | Some x, l -> Some (x,l)
       | None, [] -> None
     in
     let guard = match guard with
       | Some (h,t) ->
          Some (List.fold_left (fun acc guard -> mk_exp (E_app_infix (acc, mk_id "&", guard))) h t)
       | None -> None
     in
     let checked_guard, env' = match guard with
       | None -> None, env
       | Some guard ->
          let checked_guard = check_exp env guard bool_typ in
          Some checked_guard, add_opt_constraint (assert_constraint env true checked_guard) env
     in
     let checked_case = crule check_exp env' case typ in
     construct_pexp (tpat, checked_guard, checked_case, (l, None))
  (* AA: Not sure if we still need this *)
  | exception (Type_error _ as typ_exn) ->
     match pat with
     | P_aux (P_lit lit, _) ->
        let guard' = mk_exp (E_app_infix (mk_exp (E_id (mk_id "p#")), mk_id "==", mk_exp (E_lit lit))) in
        let guard = match guard with
          | None -> guard'
          | Some guard -> mk_exp (E_app_infix (guard, mk_id "&", guard'))
        in
        check_case env pat_typ (Pat_aux (Pat_when (mk_pat (P_id (mk_id "p#")), guard, case), annot)) typ
     | _ -> raise typ_exn

and check_mpexp other_env env mpexp typ =
  let mpat,guard,((l,_) as annot) = destruct_mpexp mpexp in
  match bind_mpat false other_env env mpat typ with
  | checked_mpat, env, guards ->
     let guard = match guard, guards with
       | None, h::t -> Some (h,t)
       | Some x, l -> Some (x,l)
       | None, [] -> None
     in
     let guard = match guard with
       | Some (h,t) ->
          Some (List.fold_left (fun acc guard -> mk_exp (E_app_infix (acc, mk_id "&", guard))) h t)
       | None -> None
     in
     let checked_guard, env' = match guard with
       | None -> None, env
       | Some guard ->
          let checked_guard = check_exp env guard bool_typ in
          Some checked_guard, env
     in
     construct_mpexp (checked_mpat, checked_guard, (l, None))

(* type_coercion env exp typ takes a fully annoted (i.e. already type
   checked) expression exp, and attempts to cast (coerce) it to the
   type typ by inserting a coercion function that transforms the
   annotated expression into the correct type. Returns an annoted
   expression consisting of a type coercion function applied to exp,
   or throws a type error if the coercion cannot be performed. *)
and type_coercion env (E_aux (_, (l, _)) as annotated_exp) typ =
  let strip exp_aux = strip_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))) in
  let annot_exp exp typ' = E_aux (exp, (l, mk_expected_tannot env typ' no_effect (Some typ))) in
  let switch_exp_typ exp = match exp with
    | E_aux (exp, (l, Some tannot)) -> E_aux (exp, (l, Some { tannot with expected = Some typ }))
    | _ -> failwith "Cannot switch type for unannotated function"
  in
  let rec try_casts trigger errs = function
    | [] -> typ_raise env l (Err_no_casts (strip_exp annotated_exp, typ_of annotated_exp, typ, trigger, errs))
    | (cast :: casts) -> begin
        typ_print (lazy ("Casting with " ^ string_of_id cast ^ " expression " ^ string_of_exp annotated_exp ^ " to " ^ string_of_typ typ));
        try
          let checked_cast = crule check_exp (Env.no_casts env) (strip (E_app (cast, [annotated_exp]))) typ in
          annot_exp (E_cast (typ, checked_cast)) typ
        with
        | Type_error (_, _, err) -> try_casts trigger (err :: errs) casts
      end
  in
  begin
    try
      typ_debug (lazy ("Performing type coercion: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ));
      subtyp l env (typ_of annotated_exp) typ; switch_exp_typ annotated_exp
    with
    | Type_error (_, _, trigger) when Env.allow_casts env ->
       let casts = filter_casts env (typ_of annotated_exp) typ (Env.get_casts env) in
       try_casts trigger [] casts
    | Type_error (env, l, err) -> typ_raise env l err
  end

(* type_coercion_unify env exp typ attempts to coerce exp to a type
   exp_typ in the same way as type_coercion, except it is only
   required that exp_typ unifies with typ. Returns the annotated
   coercion as with type_coercion and also a set of unifiers, or
   throws a unification error *)
and type_coercion_unify env goals (E_aux (_, (l, _)) as annotated_exp) typ =
  let strip exp_aux = strip_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))) in
  let annot_exp exp typ' = E_aux (exp, (l, mk_expected_tannot env typ' no_effect (Some typ))) in
  let switch_typ exp typ = match exp with
    | E_aux (exp, (l, Some tannot)) -> E_aux (exp, (l, Some { tannot with typ = typ }))
    | _ -> failwith "Cannot switch type for unannotated expression"
  in
  let rec try_casts = function
    | [] -> unify_error l "No valid casts resulted in unification"
    | (cast :: casts) -> begin
        typ_print (lazy ("Casting with " ^ string_of_id cast ^ " expression " ^ string_of_exp annotated_exp ^ " for unification"));
        try
          let inferred_cast = irule infer_exp (Env.no_casts env) (strip (E_app (cast, [annotated_exp]))) in
          let ityp, env = bind_existential l None (typ_of inferred_cast) env in
          inferred_cast, unify l env (KidSet.diff goals (ambiguous_vars typ)) typ ityp, env
        with
        | Type_error (_, _, err) -> try_casts casts
        | Unification_error (_, err) -> try_casts casts
      end
  in
  begin
    try
      typ_debug (lazy ("Coercing unification: from " ^ string_of_typ (typ_of annotated_exp) ^ " to " ^ string_of_typ typ));
      let atyp, env = bind_existential l None (typ_of annotated_exp) env in
      let atyp, env = bind_tuple_existentials l None atyp env in
      annotated_exp, unify l env (KidSet.diff goals (ambiguous_vars typ)) typ atyp, env
    with
    | Unification_error (_, m) when Env.allow_casts env ->
       let casts = filter_casts env (typ_of annotated_exp) typ (Env.get_casts env) in
       try_casts casts
  end

and bind_pat_no_guard env (P_aux (_,(l,_)) as pat) typ =
  match bind_pat env pat typ with
  | _, _, _::_ -> typ_error env l "Literal patterns not supported here"
  | tpat, env, [] -> tpat, env

and bind_pat env (P_aux (pat_aux, (l, ())) as pat) (Typ_aux (typ_aux, _) as typ) =
  let (Typ_aux (typ_aux, _) as typ), env = bind_existential l (name_pat pat) typ env in
  typ_print (lazy (Util.("Binding " |> yellow |> clear) ^ string_of_pat pat ^  " to " ^ string_of_typ typ));
  let annot_pat pat typ' = P_aux (pat, (l, mk_expected_tannot env typ' no_effect (Some typ))) in
  let switch_typ pat typ = match pat with
    | P_aux (pat_aux, (l, Some tannot)) -> P_aux (pat_aux, (l, Some { tannot with typ = typ }))
    | _ -> typ_error env l "Cannot switch type for unannotated pattern"
  in
  let bind_tuple_pat (tpats, env, guards) pat typ =
    let tpat, env, guards' = bind_pat env pat typ in tpat :: tpats, env, guards' @ guards
  in
  match pat_aux with
  | P_id v ->
     begin
       (* If the identifier we're matching on is also a constructor of
          a union, that's probably a mistake, so warn about it. *)
       if Env.is_union_constructor v env then (
         Reporting.warn
           (Printf.sprintf "Identifier %s found in pattern is also a union constructor at" (string_of_id v))
           l
           (Printf.sprintf "Suggestion: Maybe you meant to match against %s() instead?" (string_of_id v))
       );
       match Env.lookup_id v env with
       | Local _ | Unbound -> annot_pat (P_id v) typ, Env.add_local v (Immutable, typ) env, []
       | Register _ ->
          typ_error env l ("Cannot shadow register in pattern " ^ string_of_pat pat)
       | Enum enum -> subtyp l env enum typ; annot_pat (P_id v) typ, env, []
     end
  | P_var (pat, typ_pat) ->
     let env, typ = bind_typ_pat env typ_pat typ in
     let typed_pat, env, guards = bind_pat env pat typ in
     annot_pat (P_var (typed_pat, typ_pat)) typ, env, guards
  | P_wild -> annot_pat P_wild typ, env, []
  | P_or (pat1, pat2) ->
     let tpat1, env1, guards1 = bind_pat (Env.no_bindings env) pat1 typ in
     let tpat2, env2, guards2 = bind_pat (Env.no_bindings env) pat2 typ in
     annot_pat (P_or (tpat1, tpat2)) typ, env, guards1 @ guards2
  | P_not pat ->
     let tpat, env', guards = bind_pat (Env.no_bindings env) pat typ in
     annot_pat (P_not(tpat)) typ, env, guards
  | P_cons (hd_pat, tl_pat) ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let hd_pat, env, hd_guards = bind_pat env hd_pat ltyp in
          let tl_pat, env, tl_guards = bind_pat env tl_pat typ in
          annot_pat (P_cons (hd_pat, tl_pat)) typ, env, hd_guards @ tl_guards
       | _ -> typ_error env l "Cannot match cons pattern against non-list type"
     end
  | P_string_append pats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id id, _) when Id.compare id (mk_id "string") = 0 ->
          let rec process_pats env = function
            | [] -> [], env, []
            | pat :: pats ->
               let pat', env, guards = bind_pat env pat typ in
               let pats', env, guards' = process_pats env pats in
               pat' :: pats', env, guards @ guards'
          in
          let pats, env, guards = process_pats env pats in
          annot_pat (P_string_append pats) typ, env, guards
       | _ -> typ_error env l "Cannot match string-append pattern against non-string type"
     end
  | P_list pats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let rec process_pats env = function
            | [] -> [], env, []
            | (pat :: pats) ->
               let pat', env, guards = bind_pat env pat ltyp in
               let pats', env, guards' = process_pats env pats in
               pat' :: pats', env, guards @ guards'
          in
          let pats, env, guards = process_pats env pats in
          annot_pat (P_list pats) typ, env, guards
       | _ -> typ_error env l ("Cannot match list pattern " ^ string_of_pat pat ^ "  against non-list type " ^ string_of_typ typ)
     end
  | P_tup [] ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id typ_id, _) when string_of_id typ_id = "unit" ->
          annot_pat (P_tup []) typ, env, []
       | _ -> typ_error env l "Cannot match unit pattern against non-unit type"
     end
  | P_tup pats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_tup typs, _) ->
          let tpats, env, guards =
            try List.fold_left2 bind_tuple_pat ([], env, []) pats typs with
            | Invalid_argument _ -> typ_error env l "Tuple pattern and tuple type have different length"
          in
          annot_pat (P_tup (List.rev tpats)) typ, env, guards
       | _ ->
          typ_error env l (Printf.sprintf "Cannot bind tuple pattern %s against non tuple type %s"
                         (string_of_pat pat) (string_of_typ typ))
     end
  | P_app (f, [pat]) when Env.is_union_constructor f env ->
     let (typq, ctor_typ) = Env.get_union_id f env in
     let quants = quant_items typq in
     begin match Env.expand_synonyms (Env.add_typquant l typq env) ctor_typ with
     | Typ_aux (Typ_fn ([arg_typ], ret_typ, _), _) ->
        begin
          try
            let goals = quant_kopts typq |> List.map kopt_kid |> KidSet.of_list in
            typ_debug (lazy ("Unifying " ^ string_of_bind (typq, ctor_typ) ^ " for pattern " ^ string_of_typ typ));
            let unifiers = unify l env goals ret_typ typ in
            let arg_typ' = subst_unifiers unifiers arg_typ in
            let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
            if not (List.for_all (solve_quant env) quants') then
              typ_raise env l (Err_unresolved_quants (f, quants', Env.get_locals env, Env.get_constraints env))
            else ();
            let ret_typ' = subst_unifiers unifiers ret_typ in
            let arg_typ', env = bind_existential l None arg_typ' env in
            let tpat, env, guards = bind_pat env pat arg_typ' in
            annot_pat (P_app (f, [tpat])) typ, env, guards
          with
          | Unification_error (l, m) -> typ_error env l ("Unification error when pattern matching against union constructor: " ^ m)
        end
     | _ -> typ_error env l ("Mal-formed constructor " ^ string_of_id f ^ " with type " ^ string_of_typ ctor_typ)
     end

  | P_app (f, pats) when Env.is_union_constructor f env ->
     (* Treat Ctor(x, y) as Ctor((x, y)) *)
     bind_pat env (P_aux (P_app (f, [mk_pat (P_tup pats)]),(l,()))) typ

  | P_app (f, pats) when Env.is_mapping f env ->
     begin
       let (typq, mapping_typ) = Env.get_val_spec f env in
       let quants = quant_items typq in
       let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with
         | Typ_tup typs -> typs
         | _ -> [typ]
       in
       match Env.expand_synonyms env mapping_typ with
       | Typ_aux (Typ_bidir (typ1, typ2, _), _) ->
          begin
            try
              typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for pattern " ^ string_of_typ typ));

              (* FIXME: There's no obvious goals here *)
              let unifiers = unify l env (tyvars_of_typ typ2) typ2 typ in
              let arg_typ' = subst_unifiers unifiers typ1 in
              let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
              if (match quants' with [] -> false | _ -> true)
              then typ_error env l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in pattern " ^ string_of_pat pat)
              else ();

              let ret_typ' = subst_unifiers unifiers typ2 in
              let tpats, env, guards =
                try List.fold_left2 bind_tuple_pat ([], env, []) pats (untuple arg_typ') with
                | Invalid_argument _ -> typ_error env l "Mapping pattern arguments have incorrect length"
              in
              annot_pat (P_app (f, List.rev tpats)) typ, env, guards
            with
            | Unification_error (l, m) ->
               try
                 typ_debug (lazy "Unifying mapping forwards failed, trying backwards.");
                 typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for pattern " ^ string_of_typ typ));
                 let unifiers = unify l env (tyvars_of_typ typ1) typ1 typ in
                 let arg_typ' = subst_unifiers unifiers typ2 in
                 let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
                 if (match quants' with [] -> false | _ -> true)
                 then typ_error env l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in pattern " ^ string_of_pat pat)
                 else ();
                 let ret_typ' = subst_unifiers unifiers typ1 in
                 let tpats, env, guards =
                   try List.fold_left2 bind_tuple_pat ([], env, []) pats (untuple arg_typ') with
                   | Invalid_argument _ -> typ_error env l "Mapping pattern arguments have incorrect length"
                 in
                 annot_pat (P_app (f, List.rev tpats)) typ, env, guards
               with
               | Unification_error (l, m) -> typ_error env l ("Unification error when pattern matching against mapping constructor: " ^ m)
          end
       | _ -> typ_error env l ("Mal-formed mapping " ^ string_of_id f)
     end

  | P_app (f, _) when (not (Env.is_union_constructor f env) && not (Env.is_mapping f env)) ->
     typ_error env l (string_of_id f ^ " is not a union constructor or mapping in pattern " ^ string_of_pat pat)
  | P_as (pat, id) ->
     let (typed_pat, env, guards) = bind_pat env pat typ in
     annot_pat (P_as (typed_pat, id)) (typ_of_pat typed_pat), Env.add_local id (Immutable, typ_of_pat typed_pat) env, guards
  (* This is a special case for flow typing when we match a constant numeric literal. *)
  | P_lit (L_aux (L_num n, _) as lit) when is_atom typ ->
     let nexp = match destruct_atom_nexp env typ with Some n -> n | None -> assert false in
     annot_pat (P_lit lit) (atom_typ (nconstant n)), Env.add_constraint (nc_eq nexp (nconstant n)) env, []
  | P_lit (L_aux (L_true, _) as lit) when is_atom_bool typ ->
     let nc = match destruct_atom_bool env typ with Some nc -> nc | None -> assert false in
     annot_pat (P_lit lit) (atom_bool_typ nc_true), Env.add_constraint nc env, []
  | P_lit (L_aux (L_false, _) as lit) when is_atom_bool typ ->
     let nc = match destruct_atom_bool env typ with Some nc -> nc | None -> assert false in
     annot_pat (P_lit lit) (atom_bool_typ nc_false), Env.add_constraint (nc_not nc) env, []
  | _ ->
     let (inferred_pat, env, guards) = infer_pat env pat in
     match subtyp l env typ (typ_of_pat inferred_pat) with
     | () -> switch_typ inferred_pat (typ_of_pat inferred_pat), env, guards
     | exception (Type_error _ as typ_exn) ->
        match pat_aux with
        | P_lit lit ->
           let var = fresh_var () in
           let guard = locate (fun _ -> l) (mk_exp (E_app_infix (mk_exp (E_id var), mk_id "==", mk_exp (E_lit lit)))) in
           let (typed_pat, env, guards) = bind_pat env (mk_pat (P_id var)) typ in
           typed_pat, env, guard::guards
        | _ -> raise typ_exn

and infer_pat env (P_aux (pat_aux, (l, ())) as pat) =
  let annot_pat pat typ = P_aux (pat, (l, mk_tannot env typ no_effect)) in
  match pat_aux with
  | P_id v ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) | Unbound ->
          typ_error env l ("Cannot infer identifier in pattern " ^ string_of_pat pat ^ " - try adding a type annotation")
       | Local (Mutable, _) | Register _ ->
          typ_error env l ("Cannot shadow mutable local or register in switch statement pattern " ^ string_of_pat pat)
       | Enum enum -> annot_pat (P_id v) enum, env, []
     end
  | P_app (f, mpats) when Env.is_union_constructor f env ->
     begin
       let (typq, ctor_typ) = Env.get_val_spec f env in
       match Env.expand_synonyms env ctor_typ with
       | Typ_aux (Typ_fn (arg_typ, ret_typ, _), _) ->
          bind_pat env pat ret_typ
       | _ -> typ_error env l ("Mal-formed constructor " ^ string_of_id f)
     end
  | P_app (f, mpats) when Env.is_mapping f env ->
     begin
       let (typq, mapping_typ) = Env.get_val_spec f env in
       match Env.expand_synonyms env mapping_typ with
       | Typ_aux (Typ_bidir (typ1, typ2, _), _) ->
          begin
            try
              bind_pat env pat typ2
            with
            | Type_error _ ->
               bind_pat env pat typ1
          end
       | _ -> typ_error env l ("Malformed mapping type " ^ string_of_id f)
     end
  | P_typ (typ_annot, pat) ->
     Env.wf_typ env typ_annot;
     let (typed_pat, env, guards) = bind_pat env pat typ_annot in
     annot_pat (P_typ (typ_annot, typed_pat)) typ_annot, env, guards
  | P_lit lit ->
     annot_pat (P_lit lit) (infer_lit env lit), env, []
  | P_vector (pat :: pats) ->
     let fold_pats (pats, env, guards) pat =
       let typed_pat, env, guards' = bind_pat env pat bit_typ in
       pats @ [typed_pat], env, guards' @ guards
     in
     let pats, env, guards = List.fold_left fold_pats ([], env, []) (pat :: pats) in
     let len = nexp_simp (nint (List.length pats)) in
     let etyp = typ_of_pat (List.hd pats) in
     (* BVS TODO: Non-bitvector P_vector *)
     List.iter (fun pat -> typ_equality l env etyp (typ_of_pat pat)) pats;
     annot_pat (P_vector pats) (bits_typ env len), env, guards
  | P_vector_concat (pat :: pats) ->
     let fold_pats (pats, env, guards) pat =
       let inferred_pat, env, guards' = infer_pat env pat in
       pats @ [inferred_pat], env, guards' @ guards
     in
     let inferred_pats, env, guards =
       List.fold_left fold_pats ([], env, []) (pat :: pats) in
     begin match destruct_any_vector_typ l env (typ_of_pat (List.hd inferred_pats)) with
     | Destruct_vector (len, _, vtyp) ->
        let fold_len len pat =
          let (len', _, vtyp') = destruct_vector_typ l env (typ_of_pat pat) in
          typ_equality l env vtyp vtyp';
          nsum len len'
        in
        let len = nexp_simp (List.fold_left fold_len len (List.tl inferred_pats)) in
        annot_pat (P_vector_concat inferred_pats) (dvector_typ env len vtyp), env, guards
     | Destruct_bitvector (len, _) ->
        let fold_len len pat =
          let (len', _) = destruct_bitvector_typ l env (typ_of_pat pat) in
          nsum len len'
        in
        let len = nexp_simp (List.fold_left fold_len len (List.tl inferred_pats)) in
        annot_pat (P_vector_concat inferred_pats) (bits_typ env len), env, guards
     end
  | P_string_append pats ->
     let fold_pats (pats, env, guards) pat =
       let inferred_pat, env, guards' = infer_pat env pat in
       typ_equality l env (typ_of_pat inferred_pat) string_typ;
       pats @ [inferred_pat], env, guards' @ guards
     in
     let typed_pats, env, guards =
       List.fold_left fold_pats ([], env, []) pats
     in
     annot_pat (P_string_append typed_pats) string_typ, env, guards
  | P_as (pat, id) ->
     let (typed_pat, env, guards) = infer_pat env pat in
     annot_pat (P_as (typed_pat, id)) (typ_of_pat typed_pat),
     Env.add_local id (Immutable, typ_of_pat typed_pat) env,
     guards
  | _ -> typ_error env l ("Couldn't infer type of pattern " ^ string_of_pat pat)

and bind_typ_pat env (TP_aux (typ_pat_aux, l) as typ_pat) (Typ_aux (typ_aux, _) as typ) =
  typ_print (lazy (Util.("Binding type pattern " |> yellow |> clear) ^ string_of_typ_pat typ_pat ^ " to " ^ string_of_typ typ));
  match typ_pat_aux, typ_aux with
  | TP_wild, _ -> env, typ
  | TP_var kid, _ ->
     begin
       match typ_nexps typ, typ_constraints typ with
       | [nexp], [] ->
          let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_int kid) env in
          let nexp = match shadow with Some s_v -> nexp_subst kid (arg_nexp (nvar s_v)) nexp | None -> nexp in
          Env.add_constraint (nc_eq (nvar kid) nexp) env, replace_nexp_typ nexp (Nexp_aux (Nexp_var kid, l)) typ
       | [], [nc] ->
          let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_bool kid) env in
          let nc = match shadow with Some s_v -> constraint_subst kid (arg_bool (nc_var s_v)) nc | None -> nc in
          Env.add_constraint (nc_and (nc_or (nc_not nc) (nc_var kid)) (nc_or nc (nc_not (nc_var kid)))) env,
          replace_nc_typ nc (NC_aux (NC_var kid, l)) typ
       | [], [] ->
          typ_error env l ("No numeric expressions in " ^ string_of_typ typ ^ " to bind " ^ string_of_kid kid ^ " to")
       | _, _ ->
          typ_error env l ("Type " ^ string_of_typ typ ^ " has multiple numeric or boolean expressions. Cannot bind " ^ string_of_kid kid)
     end
  | TP_app (f1, tpats), Typ_app (f2, typs) when Id.compare f1 f2 = 0 ->
     let env, args = List.fold_right2 (fun tp arg (env, args) -> let env, arg = bind_typ_pat_arg env tp arg in env, arg::args) tpats typs (env, []) in
     env, Typ_aux (Typ_app (f2, args), l)
  | _, _ -> typ_error env l ("Couldn't bind type " ^ string_of_typ typ ^ " with " ^ string_of_typ_pat typ_pat)
and bind_typ_pat_arg env (TP_aux (typ_pat_aux, l) as typ_pat) (A_aux (typ_arg_aux, l_arg) as typ_arg) =
  match typ_pat_aux, typ_arg_aux with
  | TP_wild, _ -> env, typ_arg
  | TP_var kid, A_nexp nexp ->
     let env, shadow = Env.add_typ_var_shadow l (mk_kopt K_int kid) env in
     let nexp = match shadow with Some s_v -> nexp_subst kid (arg_nexp (nvar s_v)) nexp | None -> nexp in
     Env.add_constraint (nc_eq (nvar kid) nexp) env, arg_nexp ~loc:l (nvar kid)
  | _, A_typ typ -> let env, typ' = bind_typ_pat env typ_pat typ in env, A_aux (A_typ typ', l_arg)
  | _, A_order _ -> typ_error env l "Cannot bind type pattern against order"
  | _, _ -> typ_error env l ("Couldn't bind type argument " ^ string_of_typ_arg typ_arg ^ " with " ^ string_of_typ_pat typ_pat)

and bind_assignment assign_l env (LEXP_aux (lexp_aux, (lexp_l, ())) as lexp) (E_aux (_, (exp_l, ())) as exp) =
  let annot_assign lexp exp = E_aux (E_assign (lexp, exp), (assign_l, mk_tannot env (mk_typ (Typ_id (mk_id "unit"))) no_effect)) in
  let annot_lexp_effect lexp typ eff = LEXP_aux (lexp, (lexp_l, mk_tannot env typ eff)) in
  let annot_lexp lexp typ = annot_lexp_effect lexp typ no_effect in
  let has_typ v env =
    match Env.lookup_id v env with
    | Local (Mutable, _) | Register _ -> true
    | _ -> false
  in
  match lexp_aux with
  | LEXP_memory (f, xs) ->
     check_exp env (E_aux (E_app (f, xs @ [exp]), (lexp_l, ()))) unit_typ, env
  | LEXP_cast (typ_annot, v) ->
     let checked_exp = crule check_exp env exp typ_annot in
     let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
     annot_assign tlexp checked_exp, env'
  | LEXP_id v when has_typ v env ->
     begin match Env.lookup_id ~raw:true v env with
     | Local (Mutable, vtyp) | Register (_, _, vtyp) ->
        let checked_exp = crule check_exp env exp vtyp in
        let tlexp, env' = bind_lexp env lexp (typ_of checked_exp) in
        annot_assign tlexp checked_exp, env'
     | _ -> assert false
     end
  | _ ->
     (* Here we have two options, we can infer the type from the
        expression, or we can infer the type from the
        l-expression. Both are useful in different cases, so try
        both. *)
     try
       let inferred_exp = irule infer_exp env exp in
       let tlexp, env' = bind_lexp env lexp (typ_of inferred_exp) in
       annot_assign tlexp inferred_exp, env'
     with
     | Type_error (_, l, err) ->
        try
          let inferred_lexp = infer_lexp env lexp in
          let checked_exp = crule check_exp env exp (lexp_typ_of inferred_lexp) in
          annot_assign inferred_lexp checked_exp, env
        with Type_error (env, l', err') -> typ_raise env l' (Err_because (err', l, err))

and bind_lexp env (LEXP_aux (lexp_aux, (l, ())) as lexp) typ =
  typ_print (lazy ("Binding mutable " ^ string_of_lexp lexp ^  " to " ^ string_of_typ typ));
  let annot_lexp_effect lexp typ eff = LEXP_aux (lexp, (l, mk_tannot env typ eff)) in
  let annot_lexp lexp typ = annot_lexp_effect lexp typ no_effect in
  match lexp_aux with
  | LEXP_cast (typ_annot, v) ->
     begin match Env.lookup_id ~raw:true v env with
       | Local (Immutable, _) | Enum _ ->
          typ_error env l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
       | Local (Mutable, vtyp) ->
          subtyp l env typ typ_annot;
          subtyp l env typ_annot vtyp;
          annot_lexp (LEXP_cast (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env
       | Register (_, weff, vtyp) ->
          subtyp l env typ typ_annot;
          subtyp l env typ_annot vtyp;
          annot_lexp_effect (LEXP_cast (typ_annot, v)) typ weff, env
       | Unbound ->
          subtyp l env typ typ_annot;
          annot_lexp (LEXP_cast (typ_annot, v)) typ, Env.add_local v (Mutable, typ_annot) env
     end
  | LEXP_id v ->
     begin match Env.lookup_id ~raw:true v env with
     | Local (Immutable, _) | Enum _ ->
        typ_error env l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
     | Local (Mutable, vtyp) -> subtyp l env typ vtyp; annot_lexp (LEXP_id v) typ, env
     | Register (_, weff, vtyp) -> subtyp l env typ vtyp; annot_lexp_effect (LEXP_id v) typ weff, env
     | Unbound -> annot_lexp (LEXP_id v) typ, Env.add_local v (Mutable, typ) env
     end
  | LEXP_tup lexps ->
     begin
       let typ = Env.expand_synonyms env typ in
       let (Typ_aux (typ_aux, _)) = typ in
       match typ_aux with
       | Typ_tup typs ->
          let bind_tuple_lexp lexp typ (tlexps, env) =
            let tlexp, env = bind_lexp env lexp typ in tlexp :: tlexps, env
          in
          let tlexps, env =
            try List.fold_right2 bind_tuple_lexp lexps typs ([], env) with
            | Invalid_argument _ -> typ_error env l "Tuple l-expression and tuple type have different length"
          in
          annot_lexp (LEXP_tup tlexps) typ, env
       | _ -> typ_error env l ("Cannot bind tuple l-expression against non tuple type " ^ string_of_typ typ)
     end
  | _ ->
     let inferred_lexp = infer_lexp env lexp in
     subtyp l env typ (lexp_typ_of inferred_lexp);
     inferred_lexp, env

and infer_lexp env (LEXP_aux (lexp_aux, (l, ())) as lexp) =
  let annot_lexp_effect lexp typ eff = LEXP_aux (lexp, (l, mk_tannot env typ eff)) in
  let annot_lexp lexp typ = annot_lexp_effect lexp typ no_effect in
  match lexp_aux with
  | LEXP_id v ->
     begin match Env.lookup_id v env with
     | Local (Mutable, typ) -> annot_lexp (LEXP_id v) typ
     (* Probably need to remove flows here *)
     | Register (_, weff, typ) -> annot_lexp_effect (LEXP_id v) typ weff
     | Local (Immutable, _) | Enum _ ->
        typ_error env l ("Cannot modify let-bound constant or enumeration constructor " ^ string_of_id v)
     | Unbound ->
        typ_error env l ("Cannot create a new identifier in this l-expression " ^ string_of_lexp lexp)
     end
  | LEXP_vector_range (v_lexp, exp1, exp2) ->
     begin
       let inferred_v_lexp = infer_lexp env v_lexp in
       let (Typ_aux (v_typ_aux, _) as v_typ) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
       match v_typ_aux with
       | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _)]) when Id.compare id (mk_id "bitvector") = 0 ->
          let inferred_exp1 = infer_exp env exp1 in
          let inferred_exp2 = infer_exp env exp2 in
          let nexp1, env = bind_numeric l (typ_of inferred_exp1) env in
          let nexp2, env = bind_numeric l (typ_of inferred_exp2) env in
          let (slice_len, check) = match ord with
            | Ord_aux (Ord_inc, _) ->
               (nexp_simp (nsum (nminus nexp2 nexp1) (nint 1)),
                nc_and (nc_and (nc_lteq (nint 0) nexp1) (nc_lteq nexp1 nexp2)) (nc_lt nexp2 len))
            | Ord_aux (Ord_dec, _) ->
               (nexp_simp (nsum (nminus nexp1 nexp2) (nint 1)),
                nc_and (nc_and (nc_lteq (nint 0) nexp2) (nc_lteq nexp2 nexp1)) (nc_lt nexp1 len))
            | Ord_aux (Ord_var _, _) ->
               typ_error env l "Slice assignment to bitvector with variable indexing order unsupported"
          in
          if !opt_no_lexp_bounds_check || prove __POS__ env check then
            annot_lexp (LEXP_vector_range (inferred_v_lexp, inferred_exp1, inferred_exp2)) (bitvector_typ slice_len ord)
          else
            typ_raise env l (Err_lexp_bounds (check, Env.get_locals env, Env.get_constraints env))
       | _ -> typ_error env l "Cannot assign slice of non vector type"
     end
  | LEXP_vector (v_lexp, exp) ->
     begin
       let inferred_v_lexp = infer_lexp env v_lexp in
       let (Typ_aux (v_typ_aux, _) as v_typ) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
       match v_typ_aux with
       | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _); A_aux (A_typ elem_typ, _)])
            when Id.compare id (mk_id "vector") = 0 ->
          let inferred_exp = infer_exp env exp in
          let nexp, env = bind_numeric l (typ_of inferred_exp) env in
          let bounds_check = nc_and (nc_lteq (nint 0) nexp) (nc_lt nexp len) in
          if !opt_no_lexp_bounds_check || prove __POS__ env bounds_check then
            annot_lexp (LEXP_vector (inferred_v_lexp, inferred_exp)) elem_typ
          else
            typ_raise env l (Err_lexp_bounds (bounds_check, Env.get_locals env, Env.get_constraints env))
       | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _)])
            when Id.compare id (mk_id "bitvector") = 0 ->
          let inferred_exp = infer_exp env exp in
          let nexp, env = bind_numeric l (typ_of inferred_exp) env in
          let bounds_check = nc_and (nc_lteq (nint 0) nexp) (nc_lt nexp len) in
          if !opt_no_lexp_bounds_check || prove __POS__ env bounds_check then
            annot_lexp (LEXP_vector (inferred_v_lexp, inferred_exp)) bit_typ
          else
            typ_raise env l (Err_lexp_bounds (bounds_check, Env.get_locals env, Env.get_constraints env))
       | Typ_id id ->
          begin match exp with
          | E_aux (E_id field, _) ->
             let (hi, lo) = Env.get_bitfield_range l id field env in
             let hi, lo = mk_exp ~loc:l (E_lit (L_aux (L_num hi, l))), mk_exp ~loc:l (E_lit (L_aux (L_num lo, l))) in
             infer_lexp env (LEXP_aux (LEXP_vector_range (LEXP_aux (LEXP_field (v_lexp, Id_aux (Id "bits", l)), (l, ())), hi, lo), (l, ())))
          | _ ->
             typ_error env l (string_of_exp exp ^ " is not a bitfield accessor")
          end
       | _ -> typ_error env l "Cannot assign vector element of non vector or bitfield type"
     end
  | LEXP_vector_concat [] -> typ_error env l "Cannot have empty vector concatenation l-expression"
  | LEXP_vector_concat (v_lexp :: v_lexps) ->
     begin
       let sum_vector_lengths first_ord first_elem_typ acc (Typ_aux (v_typ_aux, _) as v_typ) =
         match v_typ_aux with
         | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _); A_aux (A_typ elem_typ, _)])
              when Id.compare id (mk_id "vector") = 0 && ord_identical ord first_ord ->
            typ_equality l env elem_typ first_elem_typ;
            nsum acc len
         | _ -> typ_error env l "Vector concatentation l-expression must only contain vector types of the same order"
       in
       let sum_bitvector_lengths first_ord acc (Typ_aux (v_typ_aux, _) as v_typ) =
         match v_typ_aux with
         | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _)])
              when Id.compare id (mk_id "bitvector") = 0 && ord_identical ord first_ord ->
            nsum acc len
         | _ -> typ_error env l "Bitvector concatentation l-expression must only contain bitvector types of the same order"
       in
       let inferred_v_lexp = infer_lexp env v_lexp in
       let inferred_v_lexps = List.map (infer_lexp env) v_lexps in
       let (Typ_aux (v_typ_aux, _) as v_typ) = Env.expand_synonyms env (lexp_typ_of inferred_v_lexp) in
       let v_typs = List.map (fun lexp -> Env.expand_synonyms env (lexp_typ_of lexp)) inferred_v_lexps in
       match v_typ_aux with
       | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _); A_aux (A_typ elem_typ, _)])
            when Id.compare id (mk_id "vector") = 0 ->
          let len = List.fold_left (sum_vector_lengths ord elem_typ) len v_typs in
          annot_lexp (LEXP_vector_concat (inferred_v_lexp :: inferred_v_lexps)) (vector_typ (nexp_simp len) ord elem_typ)
       | Typ_app (id, [A_aux (A_nexp len, _); A_aux (A_order ord, _)])
            when Id.compare id (mk_id "bitvector") = 0 ->
          let len = List.fold_left (sum_bitvector_lengths ord) len v_typs in
          annot_lexp (LEXP_vector_concat (inferred_v_lexp :: inferred_v_lexps)) (bitvector_typ (nexp_simp len) ord)
       | _ -> typ_error env l ("Vector concatentation l-expression must only contain bitvector or vector types, found " ^ string_of_typ v_typ)
     end
  | LEXP_field ((LEXP_aux (_, (l, ())) as lexp), field_id) ->
     let inferred_lexp = infer_lexp env lexp in
     let rectyp = lexp_typ_of inferred_lexp in
     begin match lexp_typ_of inferred_lexp with
     | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
        let (typq, rectyp_q, field_typ, _) = Env.get_accessor rectyp_id field_id env in
        let unifiers = try unify l env (tyvars_of_typ rectyp_q) rectyp_q rectyp with Unification_error (l, m) -> typ_error env l ("Unification error: " ^ m) in
        let field_typ' = subst_unifiers unifiers field_typ in
        annot_lexp (LEXP_field (inferred_lexp, field_id)) field_typ'
     | _ -> typ_error env l "Field l-expression has invalid type"
     end
  | LEXP_deref exp ->
     let inferred_exp = infer_exp env exp in
     begin match typ_of inferred_exp with
     | Typ_aux (Typ_app (r, [A_aux (A_typ vtyp, _)]), _) when string_of_id r = "register" ->
        annot_lexp_effect (LEXP_deref inferred_exp) vtyp (mk_effect [BE_wreg])
     | _ ->
        typ_error env l (string_of_typ (typ_of inferred_exp)  ^ " must be a register type in " ^ string_of_exp exp ^ ")")
     end
  | LEXP_tup lexps ->
     let inferred_lexps = List.map (infer_lexp env) lexps in
     annot_lexp (LEXP_tup inferred_lexps) (tuple_typ (List.map lexp_typ_of inferred_lexps))
  | _ -> typ_error env l ("Could not infer the type of " ^ string_of_lexp lexp)

and infer_exp env (E_aux (exp_aux, (l, ())) as exp) =
  let annot_exp_effect exp typ eff = E_aux (exp, (l, mk_tannot env typ eff)) in
  let annot_exp exp typ = annot_exp_effect exp typ no_effect in
  match exp_aux with
  | E_block exps ->
     let rec last_typ = function [exp] -> typ_of exp | _ :: exps -> last_typ exps | [] -> unit_typ in
     let inferred_block = check_block l env exps None in
     annot_exp (E_block inferred_block) (last_typ inferred_block)
  | E_id v ->
     begin
       match Env.lookup_id v env with
       | Local (_, typ) | Enum typ -> annot_exp (E_id v) typ
       | Register (reff, _, typ) -> annot_exp_effect (E_id v) typ reff
       | Unbound ->
          match Bindings.find_opt v (Env.get_val_specs env) with
          | Some _ -> typ_error env l ("Identifier " ^ string_of_id v ^ " is unbound (Did you mean to call the " ^ string_of_id v ^ " function?)")
          | None -> typ_error env l ("Identifier " ^ string_of_id v ^ " is unbound")
     end
  | E_lit lit -> annot_exp (E_lit lit) (infer_lit env lit)
  | E_sizeof nexp ->
     irule infer_exp env (rewrite_sizeof l env (Env.expand_nexp_synonyms env nexp))
  | E_constraint nc ->
     Env.wf_constraint env nc;
     crule check_exp env (rewrite_nc env (Env.expand_constraint_synonyms env nc)) (atom_bool_typ nc)
  | E_field (exp, field) ->
     begin
       let inferred_exp = irule infer_exp env exp in
       match Env.expand_synonyms env (typ_of inferred_exp) with
       (* Accessing a field of a record *)
       | Typ_aux (Typ_id rectyp, _) as typ when Env.is_record rectyp env ->
          begin
            let inferred_acc = infer_funapp' l (Env.no_casts env) field (Env.get_accessor_fn rectyp field env) [strip_exp inferred_exp] None in
            match inferred_acc with
            | E_aux (E_app (field, [inferred_exp]) ,_) -> annot_exp (E_field (inferred_exp, field)) (typ_of inferred_acc)
            | _ -> assert false (* Unreachable *)
          end
       (* Not sure if we need to do anything different with args here. *)
       | Typ_aux (Typ_app (rectyp, args), _) as typ when Env.is_record rectyp env ->
          begin
            let inferred_acc = infer_funapp' l (Env.no_casts env) field (Env.get_accessor_fn rectyp field env) [strip_exp inferred_exp] None in
            match inferred_acc with
            | E_aux (E_app (field, [inferred_exp]) ,_) -> annot_exp (E_field (inferred_exp, field)) (typ_of inferred_acc)
            | _ -> assert false (* Unreachable *)
          end
       | _ ->  typ_error env l ("Field expression " ^ string_of_exp exp ^ " :: " ^ string_of_typ (typ_of inferred_exp) ^ " is not valid")
     end
  | E_tuple exps ->
     let inferred_exps = List.map (irule infer_exp env) exps in
     annot_exp (E_tuple inferred_exps) (mk_typ (Typ_tup (List.map typ_of inferred_exps)))
  | E_assign (lexp, bind) ->
     fst (bind_assignment l env lexp bind)
  | E_record_update (exp, fexps) ->
     let inferred_exp = irule infer_exp env exp in
     let typ = typ_of inferred_exp in
     let rectyp_id = match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id rectyp_id, _) | Typ_aux (Typ_app (rectyp_id, _), _) when Env.is_record rectyp_id env ->
          rectyp_id
       | _ -> typ_error env l ("The type " ^ string_of_typ typ ^ " is not a record")
     in
     let check_fexp (FE_aux (FE_Fexp (field, exp), (l, ()))) =
       let (typq, rectyp_q, field_typ, _) = Env.get_accessor rectyp_id field env in
       let unifiers = try unify l env (tyvars_of_typ rectyp_q) rectyp_q typ with Unification_error (l, m) -> typ_error env l ("Unification error: " ^ m) in
       let field_typ' = subst_unifiers unifiers field_typ in
       let inferred_exp = crule check_exp env exp field_typ' in
       FE_aux (FE_Fexp (field, inferred_exp), (l, None))
     in
     annot_exp (E_record_update (inferred_exp, List.map check_fexp fexps)) typ
  | E_cast (typ, exp) ->
     let checked_exp = crule check_exp env exp typ in
     annot_exp (E_cast (typ, checked_exp)) typ
  | E_app_infix (x, op, y) -> infer_exp env (E_aux (E_app (deinfix op, [x; y]), (l, ())))
  (* Treat a multiple argument constructor as a single argument constructor taking a tuple, Ctor(x, y) -> Ctor((x, y)). *)
  | E_app (ctor, x :: y :: zs) when Env.is_union_constructor ctor env ->
     typ_print (lazy ("Inferring multiple argument constructor: " ^ string_of_id ctor));
     irule infer_exp env (mk_exp ~loc:l (E_app (ctor, [mk_exp ~loc:l (E_tuple (x :: y :: zs))])))
  | E_app (mapping, xs) when Env.is_mapping mapping env ->
     let forwards_id = mk_id (string_of_id mapping ^ "_forwards") in
     let backwards_id = mk_id (string_of_id mapping ^ "_backwards") in
     typ_print (lazy ("Trying forwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
     begin try irule infer_exp env (E_aux (E_app (forwards_id, xs), (l, ()))) with
           | Type_error (_, _, err1) ->
              (* typ_print (lazy ("Error in forwards direction: " ^ string_of_type_error err1)); *)
              typ_print (lazy ("Trying backwards direction for mapping " ^ string_of_id mapping ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
              begin try irule infer_exp env (E_aux (E_app (backwards_id, xs), (l, ()))) with
                    | Type_error (env, _, err2) ->
                       (* typ_print (lazy ("Error in backwards direction: " ^ string_of_type_error err2)); *)
                       typ_raise env l (Err_no_overloading (mapping, [(forwards_id, err1); (backwards_id, err2)]))
              end
     end
  | E_app (f, xs) when List.length (Env.get_overloads f env) > 0 ->
     let rec try_overload = function
       | (errs, []) -> typ_raise env l (Err_no_overloading (f, errs))
       | (errs, (f :: fs)) -> begin
           typ_print (lazy ("Overload: " ^ string_of_id f ^ "(" ^ string_of_list ", " string_of_exp xs ^ ")"));
           try irule infer_exp env (E_aux (E_app (f, xs), (l, ()))) with
           | Type_error (_, _, err) ->
              typ_debug (lazy "Error");
              try_overload (errs @ [(f, err)], fs)
         end
     in
     try_overload ([], Env.get_overloads f env)
  | E_app (f, [x; y]) when string_of_id f = "and_bool" || string_of_id f = "or_bool" ->
     begin match destruct_exist (typ_of (irule infer_exp env y)) with
     | None | Some (_, NC_aux (NC_true, _), _) -> infer_funapp l env f [x; y] None
     | Some _ -> infer_funapp l env f [x; mk_exp (E_cast (bool_typ, y))] None
     | exception Type_error _ -> infer_funapp l env f [x; mk_exp (E_cast (bool_typ, y))] None
     end
  | E_app (f, xs) -> infer_funapp l env f xs None
  | E_loop (loop_type, measure, cond, body) ->
     let checked_cond = crule check_exp env cond bool_typ in
     let checked_measure = match measure with
       | Measure_aux (Measure_none,l) -> Measure_aux (Measure_none,l)
       | Measure_aux (Measure_some exp,l) ->
          Measure_aux (Measure_some (crule check_exp env exp int_typ),l)
     in
     let nc = match loop_type with
       | While -> assert_constraint env true checked_cond
       | Until -> None
     in
     let checked_body = crule check_exp (add_opt_constraint nc env) body unit_typ in
     annot_exp (E_loop (loop_type, checked_measure, checked_cond, checked_body)) unit_typ
  | E_for (v, f, t, step, ord, body) ->
     begin
       let f, t, is_dec = match ord with
         | Ord_aux (Ord_inc, _) -> f, t, false
         | Ord_aux (Ord_dec, _) -> t, f, true (* reverse direction to typechecking downto as upto loop *)
         | Ord_aux (Ord_var _, _) -> typ_error env l "Cannot check a loop with variable direction!" (* This should never happen *)
       in
       let inferred_f = irule infer_exp env f in
       let inferred_t = irule infer_exp env t in
       let checked_step = crule check_exp env step int_typ in
       match destruct_numeric (typ_of inferred_f), destruct_numeric (typ_of inferred_t) with
       | Some (kids1, nc1, nexp1), Some (kids2, nc2, nexp2) ->
          let loop_kid = mk_kid ("loop_" ^ string_of_id v) in
          let env = List.fold_left (fun env kid -> Env.add_typ_var l (mk_kopt K_int kid) env) env (loop_kid :: kids1 @ kids2) in
          let env = Env.add_constraint (nc_and nc1 nc2) env in
          let env = Env.add_constraint (nc_and (nc_lteq nexp1 (nvar loop_kid)) (nc_lteq (nvar loop_kid) nexp2)) env in
          let loop_vtyp = atom_typ (nvar loop_kid) in
          let checked_body = crule check_exp (Env.add_local v (Immutable, loop_vtyp) env) body unit_typ in
          if not is_dec (* undo reverse direction in annotated ast for downto loop *)
          then annot_exp (E_for (v, inferred_f, inferred_t, checked_step, ord, checked_body)) unit_typ
          else annot_exp (E_for (v, inferred_t, inferred_f, checked_step, ord, checked_body)) unit_typ
       | _, _ -> typ_error env l "Ranges in foreach overlap"
     end
  | E_if (cond, then_branch, else_branch) ->
     let cond' = crule check_exp env cond (mk_typ (Typ_id (mk_id "bool"))) in
     let then_branch' = irule infer_exp (add_opt_constraint (assert_constraint env true cond') env) then_branch in
     (* We don't have generic type union in Sail, but we can union simple numeric types. *)
     begin match destruct_numeric (Env.expand_synonyms env (typ_of then_branch')) with
     | Some (kids, nc, then_nexp) ->
        let then_sn = to_simple_numeric l kids nc then_nexp in
        let else_branch' = irule infer_exp (add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env) else_branch in
        begin match destruct_numeric (Env.expand_synonyms env (typ_of else_branch')) with
        | Some (kids, nc, else_nexp) ->
           let else_sn = to_simple_numeric l kids nc else_nexp in
           let typ = typ_of_simple_numeric (union_simple_numeric then_sn else_sn) in
           annot_exp (E_if (cond', then_branch', else_branch')) typ
        | None -> typ_error env l ("Could not infer type of " ^ string_of_exp else_branch)
        end
     | None ->
        begin match typ_of then_branch' with
        | Typ_aux (Typ_app (f, [_]), _) when string_of_id f = "atom_bool" ->
           let else_branch' = crule check_exp (add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env) else_branch bool_typ in
           annot_exp (E_if (cond', then_branch', else_branch')) bool_typ
        | _ ->
           let else_branch' = crule check_exp (add_opt_constraint (option_map nc_not (assert_constraint env false cond')) env) else_branch (typ_of then_branch') in
           annot_exp (E_if (cond', then_branch', else_branch')) (typ_of then_branch')
        end
     end
  | E_vector_access (v, n) ->
     begin
       try infer_exp env (E_aux (E_app (mk_id "vector_access", [v; n]), (l, ()))) with
       | Type_error (err_env, err_l, err) ->
          (try (
             let inferred_v = infer_exp env v in
             begin match typ_of inferred_v, n with
             | Typ_aux (Typ_id id, _), E_aux (E_id field, (f_l, _)) ->
                let (hi, lo) = Env.get_bitfield_range f_l id field env in
                let hi, lo = mk_exp ~loc:l (E_lit (L_aux (L_num hi, l))), mk_exp ~loc:l (E_lit (L_aux (L_num lo, l))) in
                infer_exp env (E_aux (E_vector_subrange (E_aux (E_field (v, Id_aux (Id "bits", f_l)), (l, ())), hi, lo), (l, ())))
             | _, _ ->
                typ_error env l "Vector access could not be interpreted as a bitfield access"
             end
           ) with
           | Type_error (_, err_l', err') ->
              typ_raise err_env err_l (Err_because (err, err_l', err')))
       | exn -> raise exn
     end
  | E_vector_update (v, n, exp) -> infer_exp env (E_aux (E_app (mk_id "vector_update", [v; n; exp]), (l, ())))
  | E_vector_update_subrange (v, n, m, exp) -> infer_exp env (E_aux (E_app (mk_id "vector_update_subrange", [v; n; m; exp]), (l, ())))
  | E_vector_append (v1, E_aux (E_vector [], _)) -> infer_exp env v1
  | E_vector_append (v1, v2) -> infer_exp env (E_aux (E_app (mk_id "append", [v1; v2]), (l, ())))
  | E_vector_subrange (v, n, m) -> infer_exp env (E_aux (E_app (mk_id "vector_subrange", [v; n; m]), (l, ())))
  | E_vector [] -> typ_error env l "Cannot infer type of empty vector"
  | E_vector ((item :: items) as vec) ->
     let inferred_item = irule infer_exp env item in
     let checked_items = List.map (fun i -> crule check_exp env i (typ_of inferred_item)) items in
     begin match typ_of inferred_item with
     | Typ_aux (Typ_id id, _) when string_of_id id = "bit" ->
        let bitvec_typ = bits_typ env (nint (List.length vec)) in
        annot_exp (E_vector (inferred_item :: checked_items)) bitvec_typ
     | _ ->
        let vec_typ = dvector_typ env (nint (List.length vec)) (typ_of inferred_item) in
        annot_exp (E_vector (inferred_item :: checked_items)) vec_typ
     end
  | E_assert (test, msg) ->
     let msg = assert_msg msg in
     let checked_test = crule check_exp env test bool_typ in
     let checked_msg = crule check_exp env msg string_typ in
     annot_exp_effect (E_assert (checked_test, checked_msg)) unit_typ (mk_effect [BE_escape])
  | E_internal_return exp ->
     let inferred_exp = irule infer_exp env exp in
     annot_exp (E_internal_return inferred_exp) (typ_of inferred_exp)
  | E_internal_plet (pat, bind, body) ->
     let bind_exp, ptyp = match pat with
       | P_aux (P_typ (ptyp, _), _) ->
          Env.wf_typ env ptyp;
          let checked_bind = crule check_exp env bind ptyp in
          checked_bind, ptyp
       | _ ->
          let inferred_bind = irule infer_exp env bind in
          inferred_bind, typ_of inferred_bind in
     let tpat, env = bind_pat_no_guard env pat ptyp in
     (* Propagate constraint assertions on the lhs of monadic binds to the rhs *)
     let env = match bind_exp with
       | E_aux (E_assert (constr_exp, _), _) ->
          begin
            match assert_constraint env true constr_exp with
            | Some nc ->
               typ_print (lazy ("Adding constraint " ^ string_of_n_constraint nc ^ " for assert"));
               Env.add_constraint nc env
            | None -> env
          end
       | _ -> env in
     let inferred_body = irule infer_exp env body in
     annot_exp (E_internal_plet (tpat, bind_exp, inferred_body)) (typ_of inferred_body)
  | E_let (LB_aux (letbind, (let_loc, _)), exp) ->
     let bind_exp, pat, ptyp = match letbind with
       | LB_val (P_aux (P_typ (ptyp, _), _) as pat, bind) ->
          Env.wf_typ env ptyp;
          let checked_bind = crule check_exp env bind ptyp in
          checked_bind, pat, ptyp
       | LB_val (pat, bind) ->
          let inferred_bind = irule infer_exp env bind in
          inferred_bind, pat, typ_of inferred_bind in
     check_pattern_duplicates env pat;
     let tpat, inner_env = bind_pat_no_guard env pat ptyp in
     let inferred_exp = irule infer_exp inner_env exp in
     annot_exp (E_let (LB_aux (LB_val (tpat, bind_exp), (let_loc, None)), inferred_exp))
       (check_shadow_leaks l inner_env env (typ_of inferred_exp))
  | E_ref id when Env.is_register id env ->
     let _, _, typ = Env.get_register id env in
     annot_exp (E_ref id) (register_typ typ)
  | _ -> typ_error env l ("Cannot infer type of: " ^ string_of_exp exp)

and infer_funapp l env f xs ret_ctx_typ = infer_funapp' l env f (Env.get_val_spec f env) xs ret_ctx_typ

and instantiation_of (E_aux (exp_aux, (l, tannot)) as exp) =
  match tannot with
  | Some t ->
     begin match t.instantiation with
     | Some inst -> inst
     | None ->
        raise (Reporting.err_unreachable l __POS__ "Passed non type-checked function to instantiation_of")
     end
  | _ -> invalid_arg ("instantiation_of expected application,  got " ^ string_of_exp exp)

and instantiation_of_without_type (E_aux (exp_aux, (l, _)) as exp) =
  let env = env_of exp in
  match exp_aux with
  | E_app (f, xs) -> instantiation_of (infer_funapp' l (Env.no_casts env) f (Env.get_val_spec f env) (List.map strip_exp xs) None)
  | _ -> invalid_arg ("instantiation_of expected application,  got " ^ string_of_exp exp)

and infer_funapp' l env f (typq, f_typ) xs expected_ret_typ =
  typ_print (lazy (Util.("Function " |> cyan |> clear) ^ string_of_id f));
  let annot_exp exp typ eff inst =
    E_aux (exp, (l, Some { env = env; typ = typ; effect = eff; expected = expected_ret_typ; instantiation = Some inst }))
  in
  let is_bound env kid = KBindings.mem kid (Env.get_typ_vars env) in

  (* First we record all the type variables when we start checking the
     application, so we can distinguish them from existentials
     introduced by instantiating function arguments later. *)
  let universals = Env.get_typ_vars env in
  let universal_constraints = Env.get_constraints env in

  let all_unifiers = ref KBindings.empty in
  let record_unifiers unifiers =
    let previous_unifiers = !all_unifiers in
    let updated_unifiers = KBindings.map (subst_unifiers_typ_arg unifiers) previous_unifiers in
    all_unifiers := merge_uvars l updated_unifiers unifiers;
  in

  let quants, typ_args, typ_ret, eff =
    match Env.expand_synonyms (Env.add_typquant l typq env) f_typ with
    | Typ_aux (Typ_fn (typ_args, typ_ret, eff), _) -> ref (quant_items typq), typ_args, ref typ_ret, eff
    | _ -> typ_error env l (string_of_typ f_typ ^ " is not a function type")
  in

  let unifiers = instantiate_simple_equations !quants in
  typ_debug (lazy "Instantiating from equations");
  typ_debug (lazy (string_of_list ", " (fun (kid, arg) -> string_of_kid kid ^ " => " ^ string_of_typ_arg arg) (KBindings.bindings unifiers)));
  all_unifiers := unifiers;
  let typ_args = List.map (subst_unifiers unifiers) typ_args in
  List.iter (fun unifier -> quants := instantiate_quants env !quants unifier) (KBindings.bindings unifiers);
  List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) (KBindings.bindings unifiers);

  typ_debug (lazy ("Quantifiers " ^ Util.string_of_list ", " string_of_quant_item !quants));

  let implicits, typ_args, xs =
    let typ_args' = List.filter is_not_implicit typ_args in
    match xs, typ_args' with
      (* Support the case where a function has only implicit arguments;
         allow it to be called either as f() or f(i...) *)
    | [E_aux (E_lit (L_aux (L_unit, _)), _)], [] ->
       get_implicits typ_args, [], []
    | _ ->
       if not (List.length typ_args = List.length xs) then
         if not (List.length typ_args' = List.length xs) then
           typ_error env l (Printf.sprintf "Function %s applied to %d args, expected %d (%d explicit): %s" (string_of_id f) (List.length xs) (List.length typ_args) (List.length typ_args') (String.concat ", " (List.map string_of_typ typ_args)))
         else
           get_implicits typ_args, typ_args', xs
       else
         [], List.map implicit_to_int typ_args, xs
  in

  let typ_args = match expected_ret_typ with
    | None -> typ_args
    | Some expect when is_exist (Env.expand_synonyms env expect) || is_exist !typ_ret -> typ_args
    | Some expect ->
       let goals = quant_kopts (mk_typquant !quants) |> List.map kopt_kid |> KidSet.of_list in
       try
         let unifiers = unify l env (KidSet.diff goals (ambiguous_vars !typ_ret)) !typ_ret expect in
         record_unifiers unifiers;
         let unifiers = KBindings.bindings unifiers in
         typ_debug (lazy (Util.("Unifiers " |> magenta |> clear)
                          ^ Util.string_of_list ", " (fun (v, arg) -> string_of_kid v ^ " => " ^ string_of_typ_arg arg) unifiers));
         List.iter (fun unifier -> quants := instantiate_quants env !quants unifier) unifiers;
         List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) unifiers;
         List.map (fun typ -> List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ unifiers) typ_args
       with Unification_error _ -> typ_args
  in

  (* We now iterate throught the function arguments, checking them and
     instantiating quantifiers. *)
  let instantiate env arg typ remaining_typs =
    if KidSet.for_all (is_bound env) (tyvars_of_typ typ) then
      crule check_exp env arg typ, remaining_typs, env
    else
      let goals = quant_kopts (mk_typquant !quants) |> List.map kopt_kid |> KidSet.of_list in
      typ_debug (lazy ("Quantifiers " ^ Util.string_of_list ", " string_of_quant_item !quants));
      let inferred_arg = irule infer_exp env arg in
      let inferred_arg, unifiers, env =
        try type_coercion_unify env goals inferred_arg typ with
        | Unification_error (l, m) -> typ_error env l m
      in
      record_unifiers unifiers;
      let unifiers = KBindings.bindings unifiers in
      typ_debug (lazy (Util.("Unifiers " |> magenta |> clear)
                       ^ Util.string_of_list ", " (fun (v, arg) -> string_of_kid v ^ " => " ^ string_of_typ_arg arg) unifiers));
      List.iter (fun unifier -> quants := instantiate_quants env !quants unifier) unifiers;
      List.iter (fun (v, arg) -> typ_ret := typ_subst v arg !typ_ret) unifiers;
      let remaining_typs =
        List.map (fun typ -> List.fold_left (fun typ (v, arg) -> typ_subst v arg typ) typ unifiers) remaining_typs
      in
      inferred_arg, remaining_typs, env
  in
  let fold_instantiate (xs, args, env) x =
    match args with
    | arg :: remaining_args ->
       let x, remaining_args, env = instantiate env x arg remaining_args in
       (x :: xs, remaining_args, env)
    | [] -> raise (Reporting.err_unreachable l __POS__ "Empty arguments during instantiation")
  in
  let xs, _, env = List.fold_left fold_instantiate ([], typ_args, env) xs in
  let xs = List.rev xs in

  let solve_implicit impl = match KBindings.find_opt impl !all_unifiers with
    | Some (A_aux (A_nexp (Nexp_aux (Nexp_constant c, _)), _)) -> irule infer_exp env (mk_lit_exp (L_num c))
    | Some (A_aux (A_nexp n, _)) -> irule infer_exp env (mk_exp (E_sizeof n))
    | _ -> typ_error env l ("Cannot solve implicit " ^ string_of_kid impl ^ " in " ^ string_of_exp (mk_exp (E_app (f, List.map strip_exp xs))))
  in
  let xs = List.map solve_implicit implicits @ xs in

  if not (List.for_all (solve_quant env) !quants) then
    typ_raise env l (Err_unresolved_quants (f, !quants, Env.get_locals env, Env.get_constraints env))
  else ();

  let ty_vars = KBindings.bindings (Env.get_typ_vars env) |> List.map (fun (v, k) -> mk_kopt k v) in
  let existentials = List.filter (fun kopt -> not (KBindings.mem (kopt_kid kopt) universals)) ty_vars in
  let num_new_ncs = List.length (Env.get_constraints env) - List.length universal_constraints in
  let ex_constraints = take num_new_ncs (Env.get_constraints env) in

  typ_debug (lazy ("Existentials: " ^ string_of_list ", " string_of_kinded_id existentials));
  typ_debug (lazy ("Existential constraints: " ^ string_of_list ", " string_of_n_constraint ex_constraints));

  let universals = KBindings.bindings universals |> List.map fst |> KidSet.of_list in
  let typ_ret =
    if KidSet.is_empty (KidSet.of_list (List.map kopt_kid existentials)) || KidSet.is_empty (KidSet.diff (tyvars_of_typ !typ_ret) universals)
    then !typ_ret
    else mk_typ (Typ_exist (existentials, List.fold_left nc_and nc_true ex_constraints, !typ_ret))
  in
  let typ_ret = simp_typ typ_ret in
  let exp = annot_exp (E_app (f, xs)) typ_ret eff !all_unifiers in
  typ_debug (lazy ("Returning: " ^ string_of_exp exp));
  exp

and bind_mpat allow_unknown other_env env (MP_aux (mpat_aux, (l, ())) as mpat) (Typ_aux (typ_aux, _) as typ) =
  let (Typ_aux (typ_aux, _) as typ), env = bind_existential l None typ env in
  typ_print (lazy (Util.("Binding " |> yellow |> clear) ^ string_of_mpat mpat ^  " to " ^ string_of_typ typ));
  let annot_mpat mpat typ' = MP_aux (mpat, (l, mk_expected_tannot env typ' no_effect (Some typ))) in
  let switch_typ mpat typ = match mpat with
    | MP_aux (pat_aux, (l, Some tannot)) -> MP_aux (pat_aux, (l, Some { tannot with typ = typ }))
    | _ -> typ_error env l "Cannot switch type for unannotated mapping-pattern"
  in
  let bind_tuple_mpat (tpats, env, guards) mpat typ =
    let tpat, env, guards' = bind_mpat allow_unknown other_env env mpat typ in tpat :: tpats, env, guards' @ guards
  in
  match mpat_aux with
  | MP_id v ->
     begin
       (* If the identifier we're matching on is also a constructor of
          a union, that's probably a mistake, so warn about it. *)
       if Env.is_union_constructor v env then
         Reporting.warn (Printf.sprintf "Identifier %s found in mapping-pattern is also a union constructor at"
                                        (string_of_id v))
                        l ""
       else ();
       match Env.lookup_id v env with
       | Local (Immutable, _) | Unbound -> annot_mpat (MP_id v) typ, Env.add_local v (Immutable, typ) env, []
       | Local (Mutable, _) | Register _ ->
          typ_error env l ("Cannot shadow mutable local or register in switch statement mapping-pattern " ^ string_of_mpat mpat)
       | Enum enum -> subtyp l env enum typ; annot_mpat (MP_id v) typ, env, []
     end
  | MP_cons (hd_mpat, tl_mpat) ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let hd_mpat, env, hd_guards = bind_mpat allow_unknown other_env env hd_mpat ltyp in
          let tl_mpat, env, tl_guards = bind_mpat allow_unknown other_env env tl_mpat typ in
          annot_mpat (MP_cons (hd_mpat, tl_mpat)) typ, env, hd_guards @ tl_guards
       | _ -> typ_error env l "Cannot match cons mapping-pattern against non-list type"
     end
  | MP_string_append mpats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id id, _) when Id.compare id (mk_id "string") = 0 ->
          let rec process_mpats env = function
            | [] -> [], env, []
            | pat :: pats ->
               let pat', env, guards = bind_mpat allow_unknown other_env env pat typ in
               let pats', env, guards' = process_mpats env pats in
               pat' :: pats', env, guards @ guards'
          in
          let pats, env, guards = process_mpats env mpats in
          annot_mpat (MP_string_append pats) typ, env, guards
       | _ -> typ_error env l "Cannot match string-append pattern against non-string type"
     end
  | MP_list mpats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_app (f, [A_aux (A_typ ltyp, _)]), _) when Id.compare f (mk_id "list") = 0 ->
          let rec process_mpats env = function
            | [] -> [], env, []
            | (pat :: mpats) ->
               let mpat', env, guards = bind_mpat allow_unknown other_env env mpat ltyp in
               let mpats', env, guards' = process_mpats env mpats in
               mpat' :: mpats', env, guards @ guards'
          in
          let mpats, env, guards = process_mpats env mpats in
          annot_mpat (MP_list mpats) typ, env, guards
       | _ -> typ_error env l ("Cannot match list mapping-pattern " ^ string_of_mpat mpat ^ "  against non-list type " ^ string_of_typ typ)
     end
  | MP_tup [] ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_id typ_id, _) when string_of_id typ_id = "unit" ->
          annot_mpat (MP_tup []) typ, env, []
       | _ -> typ_error env l "Cannot match unit mapping-pattern against non-unit type"
     end
  | MP_tup mpats ->
     begin
       match Env.expand_synonyms env typ with
       | Typ_aux (Typ_tup typs, _) ->
          let tpats, env, guards =
            try List.fold_left2 bind_tuple_mpat ([], env, []) mpats typs with
            | Invalid_argument _ -> typ_error env l "Tuple mapping-pattern and tuple type have different length"
          in
          annot_mpat (MP_tup (List.rev tpats)) typ, env, guards
       | _ -> typ_error env l "Cannot bind tuple mapping-pattern against non tuple type"
     end
  | MP_app (f, mpats) when Env.is_union_constructor f env ->
     begin
       let (typq, ctor_typ) = Env.get_val_spec f env in
       let quants = quant_items typq in
       let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with
         | Typ_tup typs -> typs
         | _ -> [typ]
       in
       match Env.expand_synonyms env ctor_typ with
       | Typ_aux (Typ_fn ([arg_typ], ret_typ, _), _) ->
          begin
            try
              typ_debug (lazy ("Unifying " ^ string_of_bind (typq, ctor_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
              let unifiers = unify l env (tyvars_of_typ ret_typ) ret_typ typ in
              let arg_typ' = subst_unifiers unifiers arg_typ in
              let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
              if (match quants' with [] -> false | _ -> true)
              then typ_error env l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in mapping-pattern " ^ string_of_mpat mpat)
              else ();
              let ret_typ' = subst_unifiers unifiers ret_typ in
              let tpats, env, guards =
                try List.fold_left2 bind_tuple_mpat ([], env, []) mpats (untuple arg_typ') with
                | Invalid_argument _ -> typ_error env l "Union constructor mapping-pattern arguments have incorrect length"
              in
              annot_mpat (MP_app (f, List.rev tpats)) typ, env, guards
            with
            | Unification_error (l, m) -> typ_error env l ("Unification error when mapping-pattern matching against union constructor: " ^ m)
          end
       | _ -> typ_error env l ("Mal-formed constructor " ^ string_of_id f ^ " with type " ^ string_of_typ ctor_typ)
     end
  | MP_app (other, mpats) when Env.is_mapping other env ->
     begin
       let (typq, mapping_typ) = Env.get_val_spec other env in
       let quants = quant_items typq in
       let untuple (Typ_aux (typ_aux, _) as typ) = match typ_aux with
         | Typ_tup typs -> typs
         | _ -> [typ]
       in
       match Env.expand_synonyms env mapping_typ with
       | Typ_aux (Typ_bidir (typ1, typ2, _), _) ->
          begin
            try
              typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
              let unifiers = unify l env (tyvars_of_typ typ2) typ2 typ in
              let arg_typ' = subst_unifiers unifiers typ1 in
              let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
              if (match quants' with [] -> false | _ -> true)
              then typ_error env l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in mapping-pattern " ^ string_of_mpat mpat)
              else ();
              let ret_typ' = subst_unifiers unifiers typ2 in
              let tpats, env, guards =
                try List.fold_left2 bind_tuple_mpat ([], env, []) mpats (untuple arg_typ') with
                | Invalid_argument _ -> typ_error env l "Mapping pattern arguments have incorrect length"
              in
              annot_mpat (MP_app (other, List.rev tpats)) typ, env, guards
            with
            | Unification_error (l, m) ->
               try
                 typ_debug (lazy "Unifying mapping forwards failed, trying backwards.");
                 typ_debug (lazy ("Unifying " ^ string_of_bind (typq, mapping_typ) ^ " for mapping-pattern " ^ string_of_typ typ));
                 let unifiers = unify l env (tyvars_of_typ typ1) typ1 typ in
                 let arg_typ' = subst_unifiers unifiers typ2 in
                 let quants' = List.fold_left (instantiate_quants env) quants (KBindings.bindings unifiers) in
                 if (match quants' with [] -> false | _ -> true)
                 then typ_error env l ("Quantifiers " ^ string_of_list ", " string_of_quant_item quants' ^ " not resolved in mapping-pattern " ^ string_of_mpat mpat)
                 else ();
                 let ret_typ' = subst_unifiers unifiers typ1 in
                 let tpats, env, guards =
                   try List.fold_left2 bind_tuple_mpat ([], env, []) mpats (untuple arg_typ') with
                   | Invalid_argument _ -> typ_error env l "Mapping pattern arguments have incorrect length"
                 in
                 annot_mpat (MP_app (other, List.rev tpats)) typ, env, guards
               with
               | Unification_error (l, m) -> typ_error env l ("Unification error when pattern matching against mapping constructor: " ^ m)
          end
       | Typ_aux (typ, _) ->
          typ_error env l ("unifying mapping type, expanded synonyms to non-mapping type??")
     end
  | MP_app (f, _) when not (Env.is_union_constructor f env || Env.is_mapping f env) ->
     typ_error env l (string_of_id f ^ " is not a union constructor or mapping in mapping-pattern " ^ string_of_mpat mpat)
  | MP_as (mpat, id) ->
     let (typed_mpat, env, guards) = bind_mpat allow_unknown other_env env mpat typ in
     (annot_mpat (MP_as (typed_mpat, id)) (typ_of_mpat typed_mpat),
      Env.add_local id (Immutable, typ_of_mpat typed_mpat) env,
      guards)
  (* This is a special case for flow typing when we match a constant numeric literal. *)
  | MP_lit (L_aux (L_num n, _) as lit) when is_atom typ ->
     let nexp = match destruct_atom_nexp env typ with Some n -> n | None -> assert false in
     annot_mpat (MP_lit lit) (atom_typ (nconstant n)), Env.add_constraint (nc_eq nexp (nconstant n)) env, []
  (* Similarly, for boolean literals *)
  | MP_lit (L_aux (L_true, _) as lit) when is_atom_bool typ ->
     let nc = match destruct_atom_bool env typ with Some n -> n | None -> assert false in
     annot_mpat (MP_lit lit) (atom_bool_typ nc_true), Env.add_constraint nc env, []
  | MP_lit (L_aux (L_false, _) as lit) when is_atom_bool typ ->
     let nc = match destruct_atom_bool env typ with Some n -> n | None -> assert false in
     annot_mpat (MP_lit lit) (atom_bool_typ nc_false), Env.add_constraint (nc_not nc) env, []
  | _ ->
     let (inferred_mpat, env, guards) = infer_mpat allow_unknown other_env env mpat in
     match subtyp l env typ (typ_of_mpat inferred_mpat) with
     | () -> switch_typ inferred_mpat (typ_of_mpat inferred_mpat), env, guards
     | exception (Type_error _ as typ_exn) ->
        match mpat_aux with
        | MP_lit lit ->
           let var = fresh_var () in
           let guard = mk_exp (E_app_infix (mk_exp (E_id var), mk_id "==", mk_exp (E_lit lit))) in
           let (typed_mpat, env, guards) = bind_mpat allow_unknown other_env env (mk_mpat (MP_id var)) typ in
           typed_mpat, env, guard::guards
        | _ -> raise typ_exn
and infer_mpat allow_unknown other_env env (MP_aux (mpat_aux, (l, ())) as mpat) =
  let annot_mpat mpat typ = MP_aux (mpat, (l, mk_tannot env typ no_effect)) in
  match mpat_aux with
  | MP_id v ->
     begin
       match Env.lookup_id v env with
       | Local (Immutable, _) | Unbound ->
          begin match Env.lookup_id v other_env with
          | Local (Immutable, typ) -> bind_mpat allow_unknown other_env env (mk_mpat (MP_typ (mk_mpat (MP_id v), typ))) typ
          | Unbound ->
             if allow_unknown then annot_mpat (MP_id v) unknown_typ, env, [] else
               typ_error env l ("Cannot infer identifier in mapping-pattern " ^ string_of_mpat mpat ^ " - try adding a type annotation")
          | _ -> assert false
          end
       | Local (Mutable, _) | Register _ ->
          typ_error env l ("Cannot shadow mutable local or register in mapping-pattern " ^ string_of_mpat mpat)
       | Enum enum -> annot_mpat (MP_id v) enum, env, []
     end
  | MP_app (f, mpats) when Env.is_union_constructor f env ->
     begin
       let (typq, ctor_typ) = Env.get_val_spec f env in
       match Env.expand_synonyms env ctor_typ with
       | Typ_aux (Typ_fn (arg_typ, ret_typ, _), _) ->
          bind_mpat allow_unknown other_env env mpat ret_typ
       | _ -> typ_error env l ("Mal-formed constructor " ^ string_of_id f)
     end
  | MP_app (f, mpats) when Env.is_mapping f env ->
     begin
       let (typq, mapping_typ) = Env.get_val_spec f env in
       match Env.expand_synonyms env mapping_typ with
       | Typ_aux (Typ_bidir (typ1, typ2, _), _) ->
          begin
            try
              bind_mpat allow_unknown other_env env mpat typ2
            with
            | Type_error _ ->
               bind_mpat allow_unknown other_env env mpat typ1
          end
       | _ -> typ_error env l ("Malformed mapping type " ^ string_of_id f)
     end
  | MP_lit lit ->
     annot_mpat (MP_lit lit) (infer_lit env lit), env, []
  | MP_typ (mpat, typ_annot) ->
     Env.wf_typ env typ_annot;
     let (typed_mpat, env, guards) = bind_mpat allow_unknown other_env env mpat typ_annot in
     annot_mpat (MP_typ (typed_mpat, typ_annot)) typ_annot, env, guards
  | MP_vector (mpat :: mpats) ->
     let fold_mpats (mpats, env, guards) mpat =
       let typed_mpat, env, guards' = bind_mpat allow_unknown other_env env mpat bit_typ in
       mpats @ [typed_mpat], env, guards' @ guards
     in
     let mpats, env, guards = List.fold_left fold_mpats ([], env, []) (mpat :: mpats) in
     let len = nexp_simp (nint (List.length mpats)) in
     let etyp = typ_of_mpat (List.hd mpats) in
     List.iter (fun mpat -> typ_equality l env etyp (typ_of_mpat mpat)) mpats;
     annot_mpat (MP_vector mpats) (dvector_typ env len etyp), env, guards
  | MP_vector_concat (mpat :: mpats) ->
     let fold_mpats (mpats, env, guards) mpat =
       let inferred_mpat, env, guards' = infer_mpat allow_unknown other_env env mpat in
       mpats @ [inferred_mpat], env, guards' @ guards
     in
     let inferred_mpats, env, guards =
       List.fold_left fold_mpats ([], env, []) (mpat :: mpats) in
     if allow_unknown && List.exists (fun mpat -> is_unknown_type (typ_of_mpat mpat)) inferred_mpats then
       annot_mpat (MP_vector_concat inferred_mpats) unknown_typ, env, guards (* hack *)
     else
       begin match destruct_any_vector_typ l env (typ_of_mpat (List.hd inferred_mpats)) with
       | Destruct_vector (len, _, vtyp) ->
          let fold_len len mpat =
            let (len', _, vtyp') = destruct_vector_typ l env (typ_of_mpat mpat) in
            typ_equality l env vtyp vtyp';
            nsum len len'
          in
          let len = nexp_simp (List.fold_left fold_len len (List.tl inferred_mpats)) in
          annot_mpat (MP_vector_concat inferred_mpats) (dvector_typ env len vtyp), env, guards
       | Destruct_bitvector (len, _) ->
          let fold_len len mpat =
            let (len', _) = destruct_bitvector_typ l env (typ_of_mpat mpat) in
            nsum len len'
          in
          let len = nexp_simp (List.fold_left fold_len len (List.tl inferred_mpats)) in
          annot_mpat (MP_vector_concat inferred_mpats) (bits_typ env len), env, guards
       end
  | MP_string_append mpats ->
     let fold_pats (pats, env, guards) pat =
       let inferred_pat, env, guards' = infer_mpat allow_unknown other_env env pat in
       typ_equality l env (typ_of_mpat inferred_pat) string_typ;
       pats @ [inferred_pat], env, guards' @ guards
     in
     let typed_mpats, env, guards =
       List.fold_left fold_pats ([], env, []) mpats
     in
     annot_mpat (MP_string_append typed_mpats) string_typ, env, guards
  | MP_as (mpat, id) ->
     let (typed_mpat, env, guards) = infer_mpat allow_unknown other_env env mpat in
     (annot_mpat (MP_as (typed_mpat, id)) (typ_of_mpat typed_mpat),
      Env.add_local id (Immutable, typ_of_mpat typed_mpat) env,
      guards)

  | _ ->
     typ_error env l ("Couldn't infer type of mapping-pattern " ^ string_of_mpat mpat)

(**************************************************************************)
(* 6. Effect system                                                       *)
(**************************************************************************)

let effect_of_annot = function
| Some t -> t.effect
| None -> no_effect

let effect_of (E_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect_annot annot eff = match annot with
  | Some tannot -> Some { tannot with effect = union_effects eff tannot.effect }
  | None -> None

let add_effect (E_aux (exp, (l, annot))) eff =
  E_aux (exp, (l, add_effect_annot annot eff))

let effect_of_lexp (LEXP_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect_lexp (LEXP_aux (lexp, (l, annot))) eff =
  LEXP_aux (lexp, (l, add_effect_annot annot eff))

let effect_of_pat (P_aux (exp, (l, annot))) = effect_of_annot annot
let effect_of_mpat (MP_aux (exp, (l, annot))) = effect_of_annot annot

let add_effect_pat (P_aux (pat, (l, annot))) eff =
  P_aux (pat, (l, add_effect_annot annot eff))

let add_effect_mpat (MP_aux (mpat, (l, annot))) eff =
  MP_aux (mpat, (l, add_effect_annot annot eff))

let collect_effects xs = List.fold_left union_effects no_effect (List.map effect_of xs)

let collect_effects_lexp xs = List.fold_left union_effects no_effect (List.map effect_of_lexp xs)

let collect_effects_pat xs = List.fold_left union_effects no_effect (List.map effect_of_pat xs)
let collect_effects_mpat xs = List.fold_left union_effects no_effect (List.map effect_of_mpat xs)

(* Traversal that propagates effects upwards through expressions *)

let rec propagate_exp_effect (E_aux (exp, annot)) =
  let p_exp, eff = propagate_exp_effect_aux exp in
  add_effect (E_aux (p_exp, annot)) eff
and propagate_exp_effect_aux = function
  | E_block xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_block p_xs, collect_effects p_xs
  | E_id id -> E_id id, no_effect
  | E_ref id -> E_ref id, no_effect
  | E_lit lit -> E_lit lit, no_effect
  | E_cast (typ, exp) ->
     let p_exp = propagate_exp_effect exp in
     E_cast (typ, p_exp), effect_of p_exp
  | E_app (id, xs) ->
     let p_xs = List.map propagate_exp_effect xs in
     E_app (id, p_xs), collect_effects p_xs
  | E_vector xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_vector p_xs, collect_effects p_xs
  | E_vector_access (v, i) ->
     let p_v = propagate_exp_effect v in
     let p_i = propagate_exp_effect i in
     E_vector_access (p_v, p_i), collect_effects [p_v; p_i]
  | E_vector_subrange (v, i, j) ->
     let p_v = propagate_exp_effect v in
     let p_i = propagate_exp_effect i in
     let p_j = propagate_exp_effect j in
     E_vector_subrange (p_v, p_i, p_j), collect_effects [p_v; p_i; p_j]
  | E_vector_update (v, i, x) ->
     let p_v = propagate_exp_effect v in
     let p_i = propagate_exp_effect i in
     let p_x = propagate_exp_effect x in
     E_vector_update (p_v, p_i, p_x), collect_effects [p_v; p_i; p_x]
  | E_vector_update_subrange (v, i, j, v') ->
     let p_v = propagate_exp_effect v in
     let p_i = propagate_exp_effect i in
     let p_j = propagate_exp_effect j in
     let p_v' = propagate_exp_effect v' in
     E_vector_update_subrange (p_v, p_i, p_j, p_v'), collect_effects [p_v; p_i; p_j; p_v']
  | E_vector_append (v1, v2) ->
     let p_v1 = propagate_exp_effect v1 in
     let p_v2 = propagate_exp_effect v2 in
     E_vector_append (p_v1, p_v2), collect_effects [p_v1; p_v2]
  | E_tuple xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_tuple p_xs, collect_effects p_xs
  | E_if (cond, t, e) ->
     let p_cond = propagate_exp_effect cond in
     let p_t = propagate_exp_effect t in
     let p_e =  propagate_exp_effect e in
     E_if (p_cond, p_t, p_e), collect_effects [p_cond; p_t; p_e]
  | E_case (exp, cases) ->
     let p_exp = propagate_exp_effect exp in
     let p_cases = List.map propagate_pexp_effect cases in
     let case_eff = List.fold_left union_effects no_effect (List.map snd p_cases) in
     E_case (p_exp, List.map fst p_cases), union_effects (effect_of p_exp) case_eff
  | E_record_update (exp, fexps) ->
     let p_exp = propagate_exp_effect exp in
     let p_fexps = List.map propagate_fexp_effect fexps in
     E_record_update (p_exp, List.map fst p_fexps),
     List.fold_left union_effects no_effect (effect_of p_exp :: List.map snd p_fexps)
  | E_record fexps ->
     let p_fexps = List.map propagate_fexp_effect fexps in
     E_record (List.map fst p_fexps),
     List.fold_left union_effects no_effect (List.map snd p_fexps)
  | E_try (exp, cases) ->
     let p_exp = propagate_exp_effect exp in
     let p_cases = List.map propagate_pexp_effect cases in
     let case_eff = List.fold_left union_effects no_effect (List.map snd p_cases) in
     E_try (p_exp, List.map fst p_cases), union_effects (effect_of p_exp) case_eff
  | E_for (v, f, t, step, ord, body) ->
     let p_f = propagate_exp_effect f in
     let p_t = propagate_exp_effect t in
     let p_step = propagate_exp_effect step in
     let p_body = propagate_exp_effect body in
     E_for (v, p_f, p_t, p_step, ord, p_body),
     collect_effects [p_f; p_t; p_step; p_body]
  | E_loop (loop_type, measure, cond, body) ->
     let p_cond = propagate_exp_effect cond in
     let () = match measure with
       | Measure_aux (Measure_some exp,l) ->
          let eff = effect_of (propagate_exp_effect exp) in
          if (BESet.is_empty (effect_set eff) || !opt_no_effects)
          then ()
          else typ_error (env_of exp) l ("Loop termination measure with effects " ^ string_of_effect eff)
       | _ -> ()
     in
     let p_body = propagate_exp_effect body in
     E_loop (loop_type, measure, p_cond, p_body),
     union_effects (effect_of p_cond) (effect_of p_body)
  | E_let (letbind, exp) ->
     let p_lb, eff = propagate_letbind_effect letbind in
     let p_exp = propagate_exp_effect exp in
     E_let (p_lb, p_exp), union_effects (effect_of p_exp) eff
  | E_cons (x, xs) ->
     let p_x = propagate_exp_effect x in
     let p_xs = propagate_exp_effect xs in
     E_cons (p_x, p_xs), union_effects (effect_of p_x) (effect_of p_xs)
  | E_list xs ->
     let p_xs = List.map propagate_exp_effect xs in
     E_list p_xs, collect_effects p_xs
  | E_assign (lexp, exp) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp = propagate_exp_effect exp in
     E_assign (p_lexp, p_exp), union_effects (effect_of p_exp) (effect_of_lexp p_lexp)
  | E_var (lexp, bind, exp) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_bind = propagate_exp_effect bind in
     let p_exp = propagate_exp_effect exp in
     E_var (p_lexp, p_bind, p_exp), union_effects (effect_of_lexp p_lexp) (collect_effects [p_bind; p_exp])
  | E_sizeof nexp -> E_sizeof nexp, no_effect
  | E_constraint nc -> E_constraint nc, no_effect
  | E_exit exp ->
     let p_exp = propagate_exp_effect exp in
     E_exit p_exp, effect_of p_exp
  | E_throw exp ->
     let p_exp = propagate_exp_effect exp in
     E_throw p_exp, effect_of p_exp
  | E_return exp ->
     let p_exp = propagate_exp_effect exp in
     E_return p_exp, effect_of p_exp
  | E_assert (test, msg) ->
     let p_test = propagate_exp_effect test in
     let p_msg = propagate_exp_effect msg in
     E_assert (p_test, p_msg), collect_effects [p_test; p_msg]
  | E_field (exp, id) ->
     let p_exp = propagate_exp_effect exp in
     E_field (p_exp, id), effect_of p_exp
  | E_internal_plet (pat, exp, body) ->
     let p_pat = propagate_pat_effect pat in
     let p_exp = propagate_exp_effect exp in
     let p_body = propagate_exp_effect body in
     E_internal_plet (p_pat, p_exp, p_body),
     union_effects (effect_of_pat p_pat) (collect_effects [p_exp; p_body])
  | E_internal_return exp ->
     let p_exp = propagate_exp_effect exp in
     E_internal_return p_exp, effect_of p_exp
  | exp_aux -> typ_error Env.empty Parse_ast.Unknown ("Unimplemented: Cannot propagate effect in expression "
                                                      ^ string_of_exp (E_aux (exp_aux, (Parse_ast.Unknown, None))))

and propagate_fexp_effect (FE_aux (FE_Fexp (id, exp), (l, _))) =
  let p_exp = propagate_exp_effect exp in
  FE_aux (FE_Fexp (id, p_exp), (l, None)), effect_of p_exp

and propagate_pexp_effect = function
  | Pat_aux (Pat_exp (pat, exp), (l, annot)) ->
     begin
       let p_pat = propagate_pat_effect pat in
       let p_exp = propagate_exp_effect exp in
       let p_eff = union_effects (effect_of_pat p_pat) (effect_of p_exp) in
       match annot with
       | Some tannot ->
          Pat_aux (Pat_exp (p_pat, p_exp), (l, Some { tannot with effect = union_effects tannot.effect p_eff })),
          union_effects tannot.effect p_eff
       | None -> Pat_aux (Pat_exp (p_pat, p_exp), (l, None)), p_eff
     end
  | Pat_aux (Pat_when (pat, guard, exp), (l, annot)) ->
     begin
       let p_pat = propagate_pat_effect pat in
       let p_guard = propagate_exp_effect guard in
       let p_exp = propagate_exp_effect exp in
       let p_eff = union_effects (effect_of_pat p_pat)
                                          (union_effects (effect_of p_guard) (effect_of p_exp))
       in
       match annot with
       | Some tannot ->
          Pat_aux (Pat_when (p_pat, p_guard, p_exp), (l, Some { tannot with effect = union_effects tannot.effect p_eff })),
          union_effects tannot.effect p_eff
       | None -> Pat_aux (Pat_when (p_pat, p_guard, p_exp), (l, None)), p_eff
     end

and propagate_mpexp_effect = function
  | MPat_aux (MPat_pat mpat, (l, annot)) ->
     begin
       let p_mpat = propagate_mpat_effect mpat in
       let p_eff = effect_of_mpat p_mpat in
       match annot with
       | Some tannot ->
          MPat_aux (MPat_pat p_mpat, (l, Some { tannot with effect = union_effects tannot.effect p_eff })),
         union_effects tannot.effect p_eff
       | None -> MPat_aux (MPat_pat p_mpat, (l, None)), p_eff
     end
  | MPat_aux (MPat_when (mpat, guard), (l, annot)) ->
     begin
       let p_mpat = propagate_mpat_effect mpat in
       let p_guard = propagate_exp_effect guard in
       let p_eff = union_effects (effect_of_mpat p_mpat) (effect_of p_guard)
       in
       match annot with
       | Some tannot ->
          MPat_aux (MPat_when (p_mpat, p_guard), (l, Some { tannot with effect = union_effects tannot.effect p_eff })),
          union_effects tannot.effect p_eff
       | None -> MPat_aux (MPat_when (p_mpat, p_guard), (l, None)), p_eff
     end

and propagate_pat_effect (P_aux (pat, annot)) =
  let p_pat, eff = propagate_pat_effect_aux pat in
  add_effect_pat (P_aux (p_pat, annot)) eff
and propagate_pat_effect_aux = function
  | P_lit lit -> P_lit lit, no_effect
  | P_wild -> P_wild, no_effect
  | P_or(pat1, pat2) ->
     let pat1' = propagate_pat_effect pat1 in
     let pat2' = propagate_pat_effect pat2 in
     (P_or (pat1', pat2'), union_effects (effect_of_pat pat1') (effect_of_pat pat2'))
  | P_not(pat) ->
     let pat' = propagate_pat_effect pat in
     (P_not(pat'), effect_of_pat pat')
  | P_cons (pat1, pat2) ->
     let p_pat1 = propagate_pat_effect pat1 in
     let p_pat2 = propagate_pat_effect pat2 in
     P_cons (p_pat1, p_pat2), union_effects (effect_of_pat p_pat1) (effect_of_pat p_pat2)
  | P_string_append pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_string_append p_pats, collect_effects_pat p_pats
  | P_as (pat, id) ->
     let p_pat = propagate_pat_effect pat in
     P_as (p_pat, id), effect_of_pat p_pat
  | P_typ (typ, pat) ->
     let p_pat = propagate_pat_effect pat in
     P_typ (typ, p_pat), effect_of_pat p_pat
  | P_id id -> P_id id, no_effect
  | P_var (pat, kid) ->
     let p_pat = propagate_pat_effect pat in
     P_var (p_pat, kid), effect_of_pat p_pat
  | P_app (id, pats) ->
     let p_pats = List.map propagate_pat_effect pats in
     P_app (id, p_pats), collect_effects_pat p_pats
  | P_tup pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_tup p_pats, collect_effects_pat p_pats
  | P_list pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_list p_pats, collect_effects_pat p_pats
  | P_vector_concat pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_vector_concat p_pats, collect_effects_pat p_pats
  | P_vector pats ->
     let p_pats = List.map propagate_pat_effect pats in
     P_vector p_pats, collect_effects_pat p_pats
                                          (*
  | _ -> raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Unimplemented: Cannot propagate effect in pat")
                                           *)

and propagate_mpat_effect (MP_aux (mpat, annot)) =
  let p_mpat, eff = propagate_mpat_effect_aux mpat in
  add_effect_mpat (MP_aux (p_mpat, annot)) eff
and propagate_mpat_effect_aux = function
  | MP_lit lit -> MP_lit lit, no_effect
  | MP_cons (mpat1, mpat2) ->
     let p_mpat1 = propagate_mpat_effect mpat1 in
     let p_mpat2 = propagate_mpat_effect mpat2 in
     MP_cons (p_mpat1, p_mpat2), union_effects (effect_of_mpat p_mpat1) (effect_of_mpat p_mpat2)
  | MP_string_append mpats ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_string_append p_mpats, collect_effects_mpat p_mpats
  | MP_id id -> MP_id id, no_effect
  | MP_app (id, mpats) ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_app (id, p_mpats), collect_effects_mpat p_mpats
  | MP_tup mpats ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_tup p_mpats, collect_effects_mpat p_mpats
  | MP_list mpats ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_list p_mpats, collect_effects_mpat p_mpats
  | MP_vector_concat mpats ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_vector_concat p_mpats, collect_effects_mpat p_mpats
  | MP_vector mpats ->
     let p_mpats = List.map propagate_mpat_effect mpats in
     MP_vector p_mpats, collect_effects_mpat p_mpats
  | MP_typ (mpat, typ) ->
     let p_mpat = propagate_mpat_effect mpat in
     MP_typ (p_mpat, typ), effect_of_mpat mpat
  | MP_as (mpat, id) ->
     let p_mpat = propagate_mpat_effect mpat in
     MP_as (p_mpat, id), effect_of_mpat mpat

and propagate_letbind_effect (LB_aux (lb, (l, annot))) =
  let p_lb, eff = propagate_letbind_effect_aux lb in
  match annot with
  | Some tannot -> LB_aux (p_lb, (l, Some { tannot with effect = eff })), eff
  | None -> LB_aux (p_lb, (l, None)), eff
and propagate_letbind_effect_aux = function
  | LB_val (pat, exp) ->
     let p_pat = propagate_pat_effect pat in
     let p_exp = propagate_exp_effect exp in
     LB_val (p_pat, p_exp),
     union_effects (effect_of_pat p_pat) (effect_of p_exp)

and propagate_lexp_effect (LEXP_aux (lexp, annot)) =
  let p_lexp, eff = propagate_lexp_effect_aux lexp in
  add_effect_lexp (LEXP_aux (p_lexp, annot)) eff
and propagate_lexp_effect_aux = function
  | LEXP_id id -> LEXP_id id, no_effect
  | LEXP_deref exp ->
     let p_exp = propagate_exp_effect exp in
     LEXP_deref p_exp, effect_of p_exp
  | LEXP_memory (id, exps) ->
     let p_exps = List.map propagate_exp_effect exps in
     LEXP_memory (id, p_exps), collect_effects p_exps
  | LEXP_cast (typ, id) -> LEXP_cast (typ, id), no_effect
  | LEXP_tup lexps ->
     let p_lexps = List.map propagate_lexp_effect lexps in
     LEXP_tup p_lexps, collect_effects_lexp p_lexps
  | LEXP_vector (lexp, exp) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp = propagate_exp_effect exp in
     LEXP_vector (p_lexp, p_exp), union_effects (effect_of p_exp) (effect_of_lexp p_lexp)
  | LEXP_vector_range (lexp, exp1, exp2) ->
     let p_lexp = propagate_lexp_effect lexp in
     let p_exp1 = propagate_exp_effect exp1 in
     let p_exp2 = propagate_exp_effect exp2 in
     LEXP_vector_range (p_lexp, p_exp1, p_exp2),
     union_effects (collect_effects [p_exp1; p_exp2]) (effect_of_lexp p_lexp)
  | LEXP_vector_concat lexps ->
     let p_lexps = List.map propagate_lexp_effect lexps in
     LEXP_vector_concat p_lexps, collect_effects_lexp p_lexps
  | LEXP_field (lexp, id) ->
     let p_lexp = propagate_lexp_effect lexp in
     LEXP_field (p_lexp, id),effect_of_lexp p_lexp

(**************************************************************************)
(* 7. Checking toplevel definitions                                       *)
(**************************************************************************)

let check_duplicate_letbinding l pat env =
  match IdSet.choose_opt (IdSet.inter (pat_ids pat) (Env.get_toplevel_lets env)) with
  | Some id ->
     typ_error env l ("Duplicate toplevel let binding " ^ string_of_id id)
  | None -> ()
     
let check_letdef orig_env (LB_aux (letbind, (l, _))) =
  typ_print (lazy ("\nChecking top-level let" |> cyan |> clear));
  begin
    match letbind with
    | LB_val (P_aux (P_typ (typ_annot, _), _) as pat, bind) ->
       check_duplicate_letbinding l pat orig_env;
       Env.wf_typ orig_env typ_annot;
       let checked_bind = propagate_exp_effect (crule check_exp orig_env (strip_exp bind) typ_annot) in
       let tpat, env = bind_pat_no_guard orig_env (strip_pat pat) typ_annot in
       if (BESet.is_empty (effect_set (effect_of checked_bind)) || !opt_no_effects)
       then
         [DEF_val (LB_aux (LB_val (tpat, checked_bind), (l, None)))], Env.add_toplevel_lets (pat_ids tpat) env
       else typ_error env l ("Top-level definition with effects " ^ string_of_effect (effect_of checked_bind))
    | LB_val (pat, bind) ->
       check_duplicate_letbinding l pat orig_env;
       let inferred_bind = propagate_exp_effect (irule infer_exp orig_env (strip_exp bind)) in
       let tpat, env = bind_pat_no_guard orig_env (strip_pat pat) (typ_of inferred_bind) in
       if (BESet.is_empty (effect_set (effect_of inferred_bind)) || !opt_no_effects)
       then
         [DEF_val (LB_aux (LB_val (tpat, inferred_bind), (l, None)))], Env.add_toplevel_lets (pat_ids tpat) env
       else typ_error env l ("Top-level definition with effects " ^ string_of_effect (effect_of inferred_bind))
  end

let check_funcl env (FCL_aux (FCL_Funcl (id, pexp), (l, _))) typ =
  match typ with
  | Typ_aux (Typ_fn (typ_args, typ_ret, eff), _) ->
     begin
       let typ_args = List.map implicit_to_int typ_args in
       let env = Env.add_ret_typ typ_ret env in
       (* We want to forbid polymorphic undefined values in all cases,
          except when type checking the specific undefined_(type)
          functions created by the -undefined_gen functions in
          initial_check.ml. Only in these functions will the rewriter
          be able to correctly re-write the polymorphic undefineds
          (due to the specific form the functions have *)
       let env =
         if Str.string_match (Str.regexp_string "undefined_") (string_of_id id) 0
         then Env.allow_polymorphic_undefineds env
         else env
       in
       (* This is one of the cases where we are allowed to treat
          function arguments as like a tuple, and maybe we
          shouldn't. *)
       let typed_pexp, prop_eff =
         match List.map implicit_to_int typ_args with
         | [typ_arg] ->
            propagate_pexp_effect (check_case env typ_arg (strip_pexp pexp) typ_ret)
         | typ_args ->
            propagate_pexp_effect (check_case env (Typ_aux (Typ_tup typ_args, l)) (strip_pexp pexp) typ_ret)
       in
       FCL_aux (FCL_Funcl (id, typed_pexp), (l, mk_expected_tannot env typ prop_eff (Some typ)))
     end
  | _ -> typ_error env l ("Function clause must have function type: " ^ string_of_typ typ ^ " is not a function type")


let check_mapcl : 'a. Env.t -> 'a mapcl -> typ -> tannot mapcl =
  fun env (MCL_aux (cl, (l, _))) typ ->
    match typ with
    | Typ_aux (Typ_bidir (typ1, typ2, _), _) -> begin
        match cl with
        | MCL_bidir (mpexp1, mpexp2) -> begin
            let testing_env = Env.set_allow_unknowns true env in
            let left_mpat, _, _ = destruct_mpexp mpexp1 in
            let _, left_id_env, _ = bind_mpat true Env.empty testing_env (strip_mpat left_mpat) typ1 in
            let right_mpat, _, _ = destruct_mpexp mpexp2 in
            let _, right_id_env, _ = bind_mpat true Env.empty testing_env (strip_mpat right_mpat) typ2 in

            let typed_mpexp1, prop_eff1 = propagate_mpexp_effect (check_mpexp right_id_env env (strip_mpexp mpexp1) typ1) in
            let typed_mpexp2, prop_eff2 = propagate_mpexp_effect (check_mpexp left_id_env env (strip_mpexp mpexp2) typ2) in
            MCL_aux (MCL_bidir (typed_mpexp1, typed_mpexp2), (l, mk_expected_tannot env typ (union_effects prop_eff1 prop_eff2) (Some typ)))
          end
        | MCL_forwards (mpexp, exp) -> begin
            let mpat, _, _ = destruct_mpexp mpexp in
            let _, mpat_env, _ = bind_mpat false Env.empty env (strip_mpat mpat) typ1 in
            let typed_mpexp, prop_eff1 = propagate_mpexp_effect (check_mpexp Env.empty env (strip_mpexp mpexp) typ1) in
            let typed_exp = propagate_exp_effect (check_exp mpat_env (strip_exp exp) typ2) in
            let prop_effs = union_effects prop_eff1 (effect_of typed_exp) in
            MCL_aux (MCL_forwards (typed_mpexp, typed_exp), (l, mk_expected_tannot env typ prop_effs (Some typ)))
          end
        | MCL_backwards (mpexp, exp) -> begin
            let mpat, _, _ = destruct_mpexp mpexp in
            let _, mpat_env, _ = bind_mpat false Env.empty env (strip_mpat mpat) typ2 in
            let typed_mpexp, prop_eff1 = propagate_mpexp_effect (check_mpexp Env.empty env (strip_mpexp mpexp) typ2) in
            let typed_exp = propagate_exp_effect (check_exp mpat_env (strip_exp exp) typ1) in
            let prop_effs = union_effects prop_eff1 (effect_of typed_exp) in
            MCL_aux (MCL_backwards (typed_mpexp, typed_exp), (l, mk_expected_tannot env typ prop_effs (Some typ)))
          end
      end
    | _ -> typ_error env l ("Mapping clause must have mapping type: " ^ string_of_typ typ ^ " is not a mapping type")

let funcl_effect (FCL_aux (FCL_Funcl (id, typed_pexp), (l, annot))) =
  match annot with
  | Some t -> t.effect
  | None -> no_effect (* Maybe could be assert false. This should never happen *)

let mapcl_effect (MCL_aux (_, (l, annot))) =
  match annot with
  | Some t -> t.effect
  | None -> no_effect (* Maybe could be assert false. This should never happen *)

let infer_funtyp l env tannotopt funcls =
  match tannotopt with
  | Typ_annot_opt_aux (Typ_annot_opt_some (quant, ret_typ), _) ->
     begin
       let rec typ_from_pat (P_aux (pat_aux, (l, _)) as pat) =
         match pat_aux with
         | P_lit lit -> infer_lit env lit
         | P_typ (typ, _) -> typ
         | P_tup pats -> mk_typ (Typ_tup (List.map typ_from_pat pats))
         | _ -> typ_error env l ("Cannot infer type from pattern " ^ string_of_pat pat)
       in
       match funcls with
       | [FCL_aux (FCL_Funcl (_, Pat_aux (pexp,_)), _)] ->
          let pat = match pexp with Pat_exp (pat,_) | Pat_when (pat,_,_) -> pat in
          (* The function syntax lets us bind multiple function
             arguments with a single pattern, hence why we need to do
             this. But perhaps we don't want to allow this? *)
          let arg_typs =
            match typ_from_pat pat with
            | Typ_aux (Typ_tup arg_typs, _) -> arg_typs
            | arg_typ -> [arg_typ]
          in
          let fn_typ = mk_typ (Typ_fn (arg_typs, ret_typ, Effect_aux (Effect_set [], Parse_ast.Unknown))) in
          (quant, fn_typ)
       | _ -> typ_error env l "Cannot infer function type for function with multiple clauses"
     end
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> typ_error env l "Cannot infer function type for unannotated function"

let mk_val_spec env typq typ id =
  let eff =
    match typ with
    | Typ_aux (Typ_fn (_,_,eff),_) -> eff
    | _ -> no_effect
  in
  DEF_spec (VS_aux (VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), Parse_ast.Unknown), id, [], false), (Parse_ast.Unknown, mk_tannot env typ eff)))

let check_tannotopt env typq ret_typ = function
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> ()
  | Typ_annot_opt_aux (Typ_annot_opt_some (annot_typq, annot_ret_typ), l) ->
     if expanded_typ_identical env ret_typ annot_ret_typ
     then ()
     else typ_error env l (string_of_bind (typq, ret_typ) ^ " and " ^ string_of_bind (annot_typq, annot_ret_typ) ^ " do not match between function and val spec")

let check_termination_measure env arg_typs pat exp =
  let typ = match arg_typs with [x] -> x | _ -> Typ_aux (Typ_tup arg_typs,Unknown) in
  let tpat, env = bind_pat_no_guard env (strip_pat pat) typ in
  let texp = check_exp env (strip_exp exp) int_typ in
  tpat, texp

let check_termination_measure_decl env (id, pat, exp) =
  let quant, typ = Env.get_val_spec id env in
  let arg_typs, l = match typ with
    | Typ_aux (Typ_fn (arg_typs, _ ,_),l) -> arg_typs,l
    | _ -> typ_error env (id_loc id) "Function val spec is not a function type"
  in
  let env = Env.add_typquant l quant env in
  let tpat, texp = check_termination_measure env arg_typs pat exp in
  DEF_measure (id, tpat, texp)

let check_fundef env (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, _)) as fd_aux) =
  let id =
    match (List.fold_right
             (fun (FCL_aux (FCL_Funcl (id, _), _)) id' ->
               match id' with
               | Some id' -> if string_of_id id' = string_of_id id then Some id'
                             else typ_error env l ("Function declaration expects all definitions to have the same name, "
                                               ^ string_of_id id ^ " differs from other definitions of " ^ string_of_id id')
               | None -> Some id) funcls None)
    with
    | Some id -> id
    | None -> typ_error env l "funcl list is empty"
  in
  typ_print (lazy ("\n" ^ Util.("Check function " |> cyan |> clear) ^ string_of_id id));
  let have_val_spec, (quant, typ), env =
    try true, Env.get_val_spec id env, env with
    | Type_error (_, l, _) ->
       let (quant, typ) = infer_funtyp l env tannotopt funcls in
       false, (quant, typ), env
  in
  let vtyp_args, vtyp_ret, declared_eff, vl = match typ with
    | Typ_aux (Typ_fn (vtyp_args, vtyp_ret, declared_eff), vl) ->
       vtyp_args, vtyp_ret, declared_eff, vl
    | _ -> typ_error env l "Function val spec is not a function type"
  in
  check_tannotopt env quant vtyp_ret tannotopt;
  typ_debug (lazy ("Checking fundef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ)));
  let funcl_env = Env.add_typquant l quant env in
  let recopt =
    match recopt with
    | Rec_aux (Rec_nonrec, l) -> Rec_aux (Rec_nonrec, l)
    | Rec_aux (Rec_rec, l) -> Rec_aux (Rec_rec, l)
    | Rec_aux (Rec_measure (measure_p, measure_e), l) ->
       let tpat, texp = check_termination_measure funcl_env vtyp_args measure_p measure_e in
       Rec_aux (Rec_measure (tpat, texp), l)
  in
  let funcls = List.map (fun funcl -> check_funcl funcl_env funcl typ) funcls in
  let eff = List.fold_left union_effects no_effect (List.map funcl_effect funcls) in
  let vs_def, env, declared_eff =
    if not have_val_spec
    then
      let typ = Typ_aux (Typ_fn (vtyp_args, vtyp_ret, eff), vl) in
      [mk_val_spec env quant typ id], Env.add_val_spec id (quant, typ) env, eff
    else [], env, declared_eff
  in
  let env = Env.define_val_spec id env in
  if (subseteq_effects eff declared_eff || !opt_no_effects)
  then
    vs_def @ [DEF_fundef (FD_aux (FD_function (recopt, tannotopt, effectopt, funcls), (l, None)))], env
  else typ_error env l ("Effects do not match: " ^ string_of_effect declared_eff ^ " declared and " ^ string_of_effect eff ^ " found")


let check_mapdef env (MD_aux (MD_mapping (id, tannot_opt, mapcls), (l, _)) as md_aux) =
  typ_print (lazy ("\nChecking mapping " ^ string_of_id id));
  let have_val_spec, (quant, typ), env =
    try true, Env.get_val_spec id env, env with
    | Type_error (_, l, _) as err ->
       match tannot_opt with
       | Typ_annot_opt_aux (Typ_annot_opt_some (quant, typ), _) ->
          false, (quant, typ), env
       | Typ_annot_opt_aux (Typ_annot_opt_none, _) ->
          raise err
  in
  let vtyp1, vtyp2, vl = match typ with
    | Typ_aux (Typ_bidir (vtyp1, vtyp2, _), vl) -> vtyp1, vtyp2, vl
    | _ -> typ_error env l "Mapping val spec was not a mapping type"
  in
  begin match tannot_opt with
  | Typ_annot_opt_aux (Typ_annot_opt_none, _) -> ()
  | Typ_annot_opt_aux (Typ_annot_opt_some (annot_typq, annot_typ), l) ->
     if expanded_typ_identical env typ annot_typ then ()
     else typ_error env l (string_of_bind (quant, typ) ^ " and " ^ string_of_bind (annot_typq, annot_typ) ^ " do not match between mapping and val spec")
  end;
  typ_debug (lazy ("Checking mapdef " ^ string_of_id id ^ " has type " ^ string_of_bind (quant, typ)));
  let vs_def, env =
    if not have_val_spec then
      [mk_val_spec env quant (Env.expand_synonyms env typ) id], Env.add_val_spec id (quant, typ) env
    else
      [], env
  in
  let mapcl_env = Env.add_typquant l quant env in
  let mapcls = List.map (fun mapcl -> check_mapcl mapcl_env mapcl typ) mapcls in
  let eff = List.fold_left union_effects no_effect (List.map mapcl_effect mapcls) in
  let env = Env.define_val_spec id env in
  vs_def @ [DEF_mapdef (MD_aux (MD_mapping (id, tannot_opt, mapcls), (l, None)))], env

let rec warn_if_unsafe_cast l env = function
  | Typ_aux (Typ_fn (arg_typs, ret_typ, _), _) ->
     List.iter (warn_if_unsafe_cast l env) arg_typs;
     warn_if_unsafe_cast l env ret_typ
  | Typ_aux (Typ_id id, _) when string_of_id id = "bool" -> ()
  | Typ_aux (Typ_id id, _) when Env.is_enum id env -> ()
  | Typ_aux (Typ_id id, _) when string_of_id id = "string" ->
     Reporting.warn "Unsafe string cast" l
       "A cast X -> string is unsafe, as it can cause 'x : X == y : X' to be checked as 'eq_string(cast(x), cast(y))'"
  (* If we have a cast to an existential, it's probably done on
     purpose and we want to avoid false positives for warnings. *)
  | Typ_aux (Typ_exist _, _) -> ()
  | typ when is_bitvector_typ typ -> ()
  | typ when is_bit_typ typ -> ()
  | typ ->
     Reporting.warn ("Potentially unsafe cast involving " ^ string_of_typ typ) l ""

(* Checking a val spec simply adds the type as a binding in the context. *)
let check_val_spec env (VS_aux (vs, (l, _))) =
  let annotate vs typq typ eff = DEF_spec (VS_aux (vs, (l, mk_tannot (Env.add_typquant l typq env) typ eff))) in
  let vs, id, typq, typ, env = match vs with
    | VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), ts_l) as typschm, id, exts, is_cast) ->
       typ_print (lazy (Util.("Check val spec " |> cyan |> clear) ^ string_of_id id ^ " : " ^ string_of_typschm typschm));
       wf_typschm env typschm;
       let env = Env.add_extern id exts env in
       let env = if is_cast then (warn_if_unsafe_cast l env (Env.expand_synonyms env typ); Env.add_cast id env) else env in
       let typq', typ' = expand_bind_synonyms ts_l env (typq, typ) in
       (* !opt_expand_valspec controls whether the actual valspec in
          the AST is expanded, the val_spec type stored in the
          environment is always expanded and uses typq' and typ' *)
       let typq, typ =
         if !opt_expand_valspec then
           (typq', typ')
         else
           (typq, typ)
       in
       let vs = VS_val_spec (TypSchm_aux (TypSchm_ts (typq, typ), ts_l), id, exts, is_cast) in
       (vs, id, typq', typ', env)
  in
  let eff =
    match typ with
    | Typ_aux (Typ_fn (_, _, eff), _) -> eff
    | _ -> no_effect
  in
  [annotate vs typq typ eff], Env.add_val_spec id (typq, typ) env

let check_default env (DT_aux (DT_order order, l)) =
  [DEF_default (DT_aux (DT_order order, l))], Env.set_default_order order env

let kinded_id_arg kind_id =
  let typ_arg arg = A_aux (arg, Parse_ast.Unknown) in
  match kind_id with
  | KOpt_aux (KOpt_kind (K_aux (K_int, _), kid), _) ->
     typ_arg (A_nexp (nvar kid))
  | KOpt_aux (KOpt_kind (K_aux (K_order, _), kid), _) ->
     typ_arg (A_order (Ord_aux (Ord_var kid, Parse_ast.Unknown)))
  | KOpt_aux (KOpt_kind (K_aux (K_type, _), kid), _) ->
     typ_arg (A_typ (mk_typ (Typ_var kid)))
  | KOpt_aux (KOpt_kind (K_aux (K_bool, _), kid), _) ->
     typ_arg (A_bool (nc_var kid))

let fold_union_quant quants (QI_aux (qi, l)) =
  match qi with
  | QI_id kind_id -> quants @ [kinded_id_arg kind_id]
  | _ -> quants

(* We wrap this around wf_binding checks that aim to forbid recursive
   types to explain any error messages raised if the well-formedness
   check fails. *)
let forbid_recursive_types type_l f =
  try f () with
  | Type_error (env, l, err) ->
     let msg = "Types are not well-formed within this type definition. Note that recursive types are forbidden." in
     raise (Type_error (env, type_l, Err_because (Err_other msg, l, err)))

let check_type_union u_l non_rec_env env variant typq (Tu_aux (tu, l)) =
  let ret_typ = app_typ variant (List.fold_left fold_union_quant [] (quant_items typq)) in
  match tu with
  | Tu_ty_id (Typ_aux (Typ_fn (arg_typ, ret_typ, _), _) as typ, v) ->
     let typq = mk_typquant (List.map (mk_qi_id K_type) (KidSet.elements (tyvars_of_typ typ))) in
     wf_binding l env (typq, typ);
     forbid_recursive_types u_l (fun () -> wf_binding l non_rec_env (typq, tuple_typ arg_typ));
     env
     |> Env.add_union_id v (typq, typ)
     |> Env.add_val_spec v (typq, typ)
  | Tu_ty_id (arg_typ, v) ->
     let typ' = mk_typ (Typ_fn ([arg_typ], ret_typ, no_effect)) in
     forbid_recursive_types u_l (fun () -> wf_binding l non_rec_env (typq, arg_typ));
     wf_binding l env (typq, typ');
     env
     |> Env.add_union_id v (typq, typ')
     |> Env.add_val_spec v (typq, typ')

let rec check_typedef : 'a. Env.t -> 'a type_def -> (tannot def) list * Env.t =
  fun env (TD_aux (tdef, (l, _))) ->
  let td_err () = raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Unimplemented Typedef") in
  match tdef with
  | TD_abbrev (id, typq, typ_arg) ->
     begin match typ_arg with
     | A_aux (A_typ typ, a_l) ->
        forbid_recursive_types l (fun () -> wf_binding a_l env (typq, typ));
     | _ -> ()
     end;
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_typ_synonym id typq typ_arg env
  | TD_record (id, typq, fields, _) ->
     forbid_recursive_types l (fun () -> List.iter (fun (Typ_aux (_, l) as field, _) -> wf_binding l env (typq, field)) fields);
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_record id typq fields env
  | TD_variant (id, typq, arms, _) ->
     let rec_env = Env.add_variant id (typq, arms) env in
     (* register_value is a special type used by theorem prover
        backends that we allow to be recursive. *)
     let non_rec_env = if string_of_id id = "register_value" then rec_env else env in
     let env =
       rec_env
       |> (fun env -> List.fold_left (fun env tu -> check_type_union l non_rec_env env id typq tu) env arms)
     in
     [DEF_type (TD_aux (tdef, (l, None)))], env
  | TD_enum (id, ids, _) ->
     [DEF_type (TD_aux (tdef, (l, None)))], Env.add_enum id ids env
  | TD_bitfield (id, typ, ranges) as unexpanded ->
     let typ = Env.expand_synonyms env typ in
     begin match typ with
     (* The type of a bitfield must be a constant-width bitvector *)
     | Typ_aux (Typ_app (v, [A_aux (A_nexp (Nexp_aux (Nexp_constant size, _)), _);
                             A_aux (A_order order, _)]), _)
          when string_of_id v = "bitvector" ->
        let size = Big_int.to_int size in
        let eval_index_nexp l nexp =
          match int_of_nexp_opt (nexp_simp (Env.expand_nexp_synonyms env nexp)) with
          | Some i -> i
          | None -> typ_error env l ("This numeric expression must evaluate to a constant: " ^ string_of_nexp nexp)
        in
        let record_tdef = TD_record (id, mk_typquant [], [(strip_typ typ, mk_id "bits")], false) in
        let ranges =
          List.fold_left (fun ranges (field, range) ->
              match range with
              | BF_aux (BF_single nexp, l) ->
                 let n = eval_index_nexp l nexp in
                 Bindings.add field (n, n) ranges
              | BF_aux (BF_range (hi, lo), l) ->
                 let hi, lo = eval_index_nexp l hi, eval_index_nexp l lo in
                 Bindings.add field (hi, lo) ranges
              | BF_aux (BF_concat _, _) ->
                 typ_error env l "Bitfield concatenation ranges are not supported"
            ) Bindings.empty ranges
        in
        let defs, env =
          (DEF_type (TD_aux (record_tdef, (l, ()))) :: Bitfield.macro id size order ranges)
          |> Initial_check.generate_undefineds IdSet.empty
          |> check_defs env
        in
        let env = Env.add_bitfield id ranges env in
        if !opt_no_bitfield_expansion
        then [DEF_type (TD_aux (unexpanded, (l, None)))], env
        else defs, env
     | _ ->
        typ_error env l "Underlying bitfield type must be a constant-width bitvector"
     end

and check_scattered : 'a. Env.t -> 'a scattered_def -> (tannot def) list * Env.t =
  fun env (SD_aux (sdef, (l, _))) ->
  match sdef with
  | SD_function _ | SD_end _ | SD_mapping _ -> [], env
  | SD_variant (id, typq) ->
     [DEF_scattered (SD_aux (SD_variant (id, typq), (l, None)))], Env.add_scattered_variant id typq env
  | SD_unioncl (id, tu) ->
     [DEF_scattered (SD_aux (SD_unioncl (id, tu), (l, None)))],
     let env = Env.add_variant_clause id tu env in
     let typq, _ = Env.get_variant id env in
     let definition_env = Env.get_scattered_variant_env id env in
     (try check_type_union l definition_env env id typq tu with
      | Type_error (env, l', err) ->
         let msg = "As this is a scattered union clause, this could \
                    also be caused by using a type defined after the \
                    'scattered union' declaration" in
         raise (Type_error (env, l', Err_because (err, id_loc id, Err_other msg))))
  | SD_funcl (FCL_aux (FCL_Funcl (id, _), (l, _)) as funcl) ->
     let typq, typ = Env.get_val_spec id env in
     let funcl_env = Env.add_typquant l typq env in
     let funcl = check_funcl funcl_env funcl typ in
     [DEF_scattered (SD_aux (SD_funcl funcl, (l, None)))], env
  | SD_mapcl (id, mapcl) ->
     let typq, typ = Env.get_val_spec id env in
     let mapcl_env = Env.add_typquant l typq env in
     let mapcl = check_mapcl mapcl_env mapcl typ in
     [DEF_scattered (SD_aux (SD_mapcl (id, mapcl), (l, None)))], env

and check_outcome : 'a. Env.t -> outcome_spec -> 'a def list -> outcome_spec * tannot def list * Env.t =
  fun env (OV_aux (OV_outcome (id, typschm, params), l)) defs ->
  typ_print (lazy (Util.("Check outcome " |> cyan |> clear) ^ string_of_id id ^ " : " ^ string_of_typschm typschm));
  match env.toplevel with
  | None ->
     begin
       incr depth;
       try
         let local_env = { (add_typ_vars l params env) with toplevel = Some l } in
         wf_typschm local_env typschm;
         let quant, typ = match typschm with
           | TypSchm_aux (TypSchm_ts (typq, typ), _) -> typq, typ
         in
         let local_env = { local_env with outcome_typschm = Some (quant, typ) } in
         let defs, _ = check_defs local_env defs in
         decr depth;
         OV_aux (OV_outcome (id, typschm, params), l), defs, Env.add_outcome id (quant, typ, params) env
       with
       | Type_error (env, err_l, err) ->
          decr depth;
          typ_raise env err_l err
     end
  | Some outer_l ->
     let msg = "Outcome must be declared within top-level scope" in
     typ_raise env l (Err_because (Err_other msg, outer_l, Err_other "Containing scope declared here"))

and check_impldef : 'a. Env.t -> 'a funcl -> tannot def list * Env.t =
  fun env (FCL_aux (FCL_Funcl (id, _), (l, _)) as funcl) ->
  typ_print (lazy (Util.("Check impl " |> cyan |> clear) ^ string_of_id id));
  match env.outcome_typschm with
  | Some (quant, typ) ->
     let funcl_env = Env.add_typquant l quant env in
     [DEF_impl (check_funcl funcl_env funcl typ)], env
  | None ->
     typ_error env l "Cannot declare an implementation outside of an outcome"

and check_outcome_instantiation : 'a. Env.t -> 'a instantiation_spec -> subst list -> tannot def list * Env.t =
  fun env (IN_aux (IN_id id, (l, _))) substs ->
  let typq, typ, params = Env.get_outcome l id env in
  let instantiate_typ substs typ =
    List.fold_left (fun typ -> function
        | IS_aux (IS_typ (kid, subst_typ), _) ->
           Env.wf_typ env subst_typ;
           typ_subst kid (mk_typ_arg (A_typ subst_typ)) typ
        | _ -> typ
      ) typ substs
  in
  [DEF_instantiation (IN_aux (IN_id id, (l, mk_tannot env unit_typ no_effect)), substs)], Env.add_val_spec id (typq, instantiate_typ substs typ) env

and check_def : 'a. Env.t -> 'a def -> tannot def list * Env.t =
  fun env def ->
  let cd_err () = raise (Reporting.err_unreachable Parse_ast.Unknown __POS__ "Unimplemented Case") in
  match def with
  | DEF_type tdef -> check_typedef env tdef
  | DEF_fixity (prec, n, op) -> [DEF_fixity (prec, n, op)], env
  | DEF_fundef fdef -> check_fundef env fdef
  | DEF_mapdef mdef -> check_mapdef env mdef
  | DEF_impl funcl -> check_impldef env funcl
  | DEF_internal_mutrec fdefs ->
     let defs = List.concat (List.map (fun fdef -> fst (check_fundef env fdef)) fdefs) in
     let split_fundef (defs, fdefs) def = match def with
       | DEF_fundef fdef -> (defs, fdefs @ [fdef])
       | _ -> (defs @ [def], fdefs) in
     let (defs, fdefs) = List.fold_left split_fundef ([], []) defs in
     (defs @ [DEF_internal_mutrec fdefs]), env
  | DEF_val letdef -> check_letdef env letdef
  | DEF_spec vs -> check_val_spec env vs
  | DEF_outcome (outcome, defs) ->
     let outcome, defs, env = check_outcome env outcome defs in
     [DEF_outcome (outcome, defs)], env
  | DEF_instantiation (ispec, substs) -> check_outcome_instantiation env ispec substs
  | DEF_default default -> check_default env default
  | DEF_overload (id, ids) -> [DEF_overload (id, ids)], Env.add_overloads id ids env
  | DEF_reg_dec (DEC_aux (DEC_reg (reffect, weffect, typ, id), (l, _))) ->
     let env = Env.add_register id reffect weffect typ env in
     [DEF_reg_dec (DEC_aux (DEC_reg (reffect, weffect, typ, id), (l, mk_expected_tannot env typ no_effect (Some typ))))], env
  | DEF_reg_dec (DEC_aux (DEC_config (id, typ, exp), (l, _))) ->
     let checked_exp = crule check_exp env (strip_exp exp) typ in
     let env = Env.add_register id no_effect (mk_effect [BE_config]) typ env in
     [DEF_reg_dec (DEC_aux (DEC_config (id, typ, checked_exp), (l, mk_expected_tannot env typ no_effect (Some typ))))], env
  | DEF_pragma (pragma, arg, l) -> [DEF_pragma (pragma, arg, l)], env
  | DEF_reg_dec (DEC_aux (DEC_alias (id, aspec), (l, annot))) -> cd_err ()
  | DEF_reg_dec (DEC_aux (DEC_typ_alias (typ, id, aspec), (l, tannot))) -> cd_err ()
  | DEF_scattered sdef -> check_scattered env sdef
  | DEF_measure (id, pat, exp) -> [check_termination_measure_decl env (id, pat, exp)], env
  | DEF_loop_measures (id, _) ->
     Reporting.unreachable (id_loc id) __POS__
       "Loop termination measures should have been rewritten before type checking"

and check_defs_progress : 'a. int -> int -> Env.t -> 'a def list -> tannot def list * Env.t =
  fun n total env defs ->
  match defs with
  | [] -> [], env
  | def :: defs ->
     Util.progress "Type check " (string_of_int n ^ "/" ^ string_of_int total) n total;
     let (def, env) = check_def env def in
     let defs, env = check_defs_progress (n + 1) total env defs in
     def @ defs, env

and check_defs : 'a. Env.t -> 'a def list -> tannot def list * Env.t =
  fun env defs -> let total = List.length defs in check_defs_progress 1 total env defs

let check : 'a. Env.t -> 'a ast -> tannot ast * Env.t =
  fun env ast ->
  let total = List.length ast.defs in
  let defs, env = check_defs_progress 1 total env ast.defs in
  { ast with defs = defs }, env

let rec check_with_envs : 'a. Env.t -> 'a def list -> (tannot def list * Env.t) list =
  fun env defs ->
  match defs with
  | [] -> []
  | def :: defs ->
     let def, env = check_def env def in
     (def, env) :: check_with_envs env defs

let initial_env =
  Env.empty
  |> Env.set_prover (Some (prove __POS__))
  |> Env.add_extern (mk_id "size_itself_int") [("_", "size_itself_int")]
  |> Env.add_val_spec (mk_id "size_itself_int")
      (TypQ_aux (TypQ_tq [QI_aux (QI_id (mk_kopt K_int (mk_kid "n")),
                                  Parse_ast.Unknown)],Parse_ast.Unknown),
       function_typ [app_typ (mk_id "itself") [mk_typ_arg (A_nexp (nvar (mk_kid "n")))]]
         (atom_typ (nvar (mk_kid "n"))) no_effect)
  |> Env.add_extern (mk_id "make_the_value") [("_", "make_the_value")]
  |> Env.add_val_spec (mk_id "make_the_value")
      (TypQ_aux (TypQ_tq [QI_aux (QI_id (mk_kopt K_int (mk_kid "n")),
                                  Parse_ast.Unknown)],Parse_ast.Unknown),
       function_typ [atom_typ (nvar (mk_kid "n"))]
         (app_typ (mk_id "itself") [mk_typ_arg (A_nexp (nvar (mk_kid "n")))]) no_effect)
  (* __assume is used by property.ml to add guards for SMT generation,
     but which don't affect flow-typing. *)
  |> Env.add_val_spec (mk_id "sail_assume")
      (TypQ_aux (TypQ_no_forall, Parse_ast.Unknown),
       function_typ [bool_typ] unit_typ no_effect)
