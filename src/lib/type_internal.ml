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

(* Note: Everything useful in this module is re-exported by other
   Type_ modules that implement the type system, so this module should
   not be imported elsewhere. *)

open Ast
open Ast_util
open Util

module Big_int = Nat_big_num

(* opt_tc_debug controls the verbosity of the type checker. 0 is
   silent, 1 prints a tree of the type derivation and 2 is like 1 but
   with much more debug information. *)
let opt_tc_debug = ref 0

let depth = ref 0

let rec indent n = match n with 0 -> "" | n -> "|   " ^ indent (n - 1)

(* Lazily evaluate debugging message. This can make a big performance
   difference; for example, repeated calls to string_of_exp can be costly for
   deeply nested expressions, e.g. with long sequences of monadic binds. *)
let typ_debug ?(level = 1) m = if !opt_tc_debug > level then prerr_endline (indent !depth ^ Lazy.force m) else ()

let typ_print m = if !opt_tc_debug > 0 then prerr_endline (indent !depth ^ Lazy.force m) else ()

let adding = Util.("Adding " |> darkgray |> clear)

type constraint_reason = (Ast.l * string) option

type type_variables = { vars : (Ast.l * kind_aux) KBindings.t; shadows : int KBindings.t }

type type_error =
  (* First parameter is the error that caused us to start doing type
     coercions, the second is the errors encountered by all possible
     coercions *)
  | Err_no_casts of uannot exp * typ * typ * type_error * type_error list
  | Err_no_overloading of id * (id * type_error) list
  | Err_unresolved_quants of id * quant_item list * (mut * typ) Bindings.t * type_variables * n_constraint list
  | Err_failed_constraint of n_constraint * (mut * typ) Bindings.t * type_variables * n_constraint list
  | Err_subtype of typ * typ * n_constraint option * (constraint_reason * n_constraint) list * type_variables
  | Err_no_num_ident of id
  | Err_other of string
  | Err_inner of type_error * Parse_ast.l * string * string option * type_error

let err_because (error1, l, error2) = Err_inner (error1, l, "Caused by", None, error2)

exception Type_error of l * type_error

let typ_error l m = raise (Type_error (l, Err_other m))

let typ_raise l err = raise (Type_error (l, err))

let string_of_bind (typquant, typ) = string_of_typquant typquant ^ ". " ^ string_of_typ typ

(* unloc_X functions remove location information from AST nodes, so we can use structural equality *)

let rec unloc_id = function
  | Id_aux (Id x, _) -> Id_aux (Id x, Parse_ast.Unknown)
  | Id_aux (Operator x, _) -> Id_aux (Operator x, Parse_ast.Unknown)

and unloc_kid = function Kid_aux (Var x, _) -> Kid_aux (Var x, Parse_ast.Unknown)

and unloc_nexp_aux = function
  | Nexp_id id -> Nexp_id (unloc_id id)
  | Nexp_var kid -> Nexp_var (unloc_kid kid)
  | Nexp_constant n -> Nexp_constant n
  | Nexp_app (id, nexps) -> Nexp_app (id, List.map unloc_nexp nexps)
  | Nexp_times (nexp1, nexp2) -> Nexp_times (unloc_nexp nexp1, unloc_nexp nexp2)
  | Nexp_sum (nexp1, nexp2) -> Nexp_sum (unloc_nexp nexp1, unloc_nexp nexp2)
  | Nexp_minus (nexp1, nexp2) -> Nexp_minus (unloc_nexp nexp1, unloc_nexp nexp2)
  | Nexp_exp nexp -> Nexp_exp (unloc_nexp nexp)
  | Nexp_neg nexp -> Nexp_neg (unloc_nexp nexp)

and unloc_nexp = function Nexp_aux (nexp_aux, _) -> Nexp_aux (unloc_nexp_aux nexp_aux, Parse_ast.Unknown)

and unloc_n_constraint_aux = function
  | NC_equal (nexp1, nexp2) -> NC_equal (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_bounded_ge (nexp1, nexp2) -> NC_bounded_ge (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_bounded_gt (nexp1, nexp2) -> NC_bounded_gt (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_bounded_le (nexp1, nexp2) -> NC_bounded_le (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_bounded_lt (nexp1, nexp2) -> NC_bounded_lt (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_not_equal (nexp1, nexp2) -> NC_not_equal (unloc_nexp nexp1, unloc_nexp nexp2)
  | NC_set (kid, nums) -> NC_set (unloc_kid kid, nums)
  | NC_or (nc1, nc2) -> NC_or (unloc_n_constraint nc1, unloc_n_constraint nc2)
  | NC_and (nc1, nc2) -> NC_and (unloc_n_constraint nc1, unloc_n_constraint nc2)
  | NC_var kid -> NC_var (unloc_kid kid)
  | NC_app (id, args) -> NC_app (unloc_id id, List.map unloc_typ_arg args)
  | NC_true -> NC_true
  | NC_false -> NC_false

and unloc_n_constraint = function NC_aux (nc_aux, _) -> NC_aux (unloc_n_constraint_aux nc_aux, Parse_ast.Unknown)

and unloc_typ_arg = function A_aux (typ_arg_aux, _) -> A_aux (unloc_typ_arg_aux typ_arg_aux, Parse_ast.Unknown)

and unloc_typ_arg_aux = function
  | A_nexp nexp -> A_nexp (unloc_nexp nexp)
  | A_typ typ -> A_typ (unloc_typ typ)
  | A_bool nc -> A_bool (unloc_n_constraint nc)

and unloc_typ_aux : typ_aux -> typ_aux = function
  | Typ_internal_unknown -> Typ_internal_unknown
  | Typ_id id -> Typ_id (unloc_id id)
  | Typ_var kid -> Typ_var (unloc_kid kid)
  | Typ_fn (arg_typs, ret_typ) -> Typ_fn (List.map unloc_typ arg_typs, unloc_typ ret_typ)
  | Typ_bidir (typ1, typ2) -> Typ_bidir (unloc_typ typ1, unloc_typ typ2)
  | Typ_tuple typs -> Typ_tuple (List.map unloc_typ typs)
  | Typ_exist (kopts, constr, typ) ->
      Typ_exist (List.map unloc_kinded_id kopts, unloc_n_constraint constr, unloc_typ typ)
  | Typ_app (id, args) -> Typ_app (unloc_id id, List.map unloc_typ_arg args)

and unloc_typ : typ -> typ = function Typ_aux (typ_aux, _) -> Typ_aux (unloc_typ_aux typ_aux, Parse_ast.Unknown)

and unloc_typq = function TypQ_aux (typq_aux, _) -> TypQ_aux (unloc_typq_aux typq_aux, Parse_ast.Unknown)

and unloc_typq_aux = function
  | TypQ_no_forall -> TypQ_no_forall
  | TypQ_tq quants -> TypQ_tq (List.map unloc_quant_item quants)

and unloc_quant_item = function QI_aux (qi_aux, _) -> QI_aux (unloc_qi_aux qi_aux, Parse_ast.Unknown)

and unloc_qi_aux = function
  | QI_id kinded_id -> QI_id (unloc_kinded_id kinded_id)
  | QI_constraint constr -> QI_constraint (unloc_n_constraint constr)

and unloc_kinded_id = function
  | KOpt_aux (kinded_id_aux, _) -> KOpt_aux (unloc_kinded_id_aux kinded_id_aux, Parse_ast.Unknown)

and unloc_kinded_id_aux = function KOpt_kind (kind, kid) -> KOpt_kind (unloc_kind kind, unloc_kid kid)

and unloc_kind = function K_aux (k_aux, _) -> K_aux (k_aux, Parse_ast.Unknown)

let rec typ_nexps (Typ_aux (typ_aux, _)) =
  match typ_aux with
  | Typ_internal_unknown -> []
  | Typ_id _ -> []
  | Typ_var _ -> []
  | Typ_tuple typs -> List.concat (List.map typ_nexps typs)
  | Typ_app (_, args) -> List.concat (List.map typ_arg_nexps args)
  | Typ_exist (_, _, typ) -> typ_nexps typ
  | Typ_fn (arg_typs, ret_typ) -> List.concat (List.map typ_nexps arg_typs) @ typ_nexps ret_typ
  | Typ_bidir (typ1, typ2) -> typ_nexps typ1 @ typ_nexps typ2

and typ_arg_nexps (A_aux (typ_arg_aux, _)) =
  match typ_arg_aux with A_nexp n -> [n] | A_typ typ -> typ_nexps typ | A_bool nc -> constraint_nexps nc

and constraint_nexps (NC_aux (nc_aux, _)) =
  match nc_aux with
  | NC_equal (n1, n2)
  | NC_bounded_ge (n1, n2)
  | NC_bounded_le (n1, n2)
  | NC_bounded_gt (n1, n2)
  | NC_bounded_lt (n1, n2)
  | NC_not_equal (n1, n2) ->
      [n1; n2]
  | NC_set _ | NC_true | NC_false | NC_var _ -> []
  | NC_or (nc1, nc2) | NC_and (nc1, nc2) -> constraint_nexps nc1 @ constraint_nexps nc2
  | NC_app (_, args) -> List.concat (List.map typ_arg_nexps args)

(* Return a KidSet containing all the type variables appearing in
   nexp, where nexp occurs underneath a Nexp_exp, i.e. 2^nexp *)
let rec nexp_power_variables (Nexp_aux (aux, _)) =
  match aux with
  | Nexp_times (n1, n2) | Nexp_sum (n1, n2) | Nexp_minus (n1, n2) ->
      KidSet.union (nexp_power_variables n1) (nexp_power_variables n2)
  | Nexp_neg n -> nexp_power_variables n
  | Nexp_id _ | Nexp_var _ | Nexp_constant _ -> KidSet.empty
  | Nexp_app (_, ns) -> List.fold_left KidSet.union KidSet.empty (List.map nexp_power_variables ns)
  | Nexp_exp n -> tyvars_of_nexp n

let constraint_power_variables nc =
  List.fold_left KidSet.union KidSet.empty (List.map nexp_power_variables (constraint_nexps nc))

let ex_counter = ref 0

let fresh_existential l k =
  let fresh = Kid_aux (Var ("'ex" ^ string_of_int !ex_counter ^ "#"), l) in
  incr ex_counter;
  mk_kopt ~loc:l k fresh

let named_existential l k = function Some n -> mk_kopt ~loc:l k (mk_kid n) | None -> fresh_existential l k

let destruct_exist_plain ?(name = None) typ =
  match typ with
  | Typ_aux (Typ_exist ([kopt], nc, typ), l) ->
      let kid, fresh = (kopt_kid kopt, named_existential l (unaux_kind (kopt_kind kopt)) name) in
      let nc = constraint_subst kid (arg_kopt fresh) nc in
      let typ = typ_subst kid (arg_kopt fresh) typ in
      Some ([fresh], nc, typ)
  | Typ_aux (Typ_exist (kopts, nc, typ), _) ->
      let add_num i = match name with Some n -> Some (n ^ string_of_int i) | None -> None in
      let fresh_kopts =
        List.mapi
          (fun i kopt -> (kopt_kid kopt, named_existential (kopt_loc kopt) (unaux_kind (kopt_kind kopt)) (add_num i)))
          kopts
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
let destruct_numeric ?(name = None) typ =
  match (destruct_exist_plain ~name typ, typ) with
  | Some (kids, nc, Typ_aux (Typ_app (id, [A_aux (A_nexp nexp, _)]), _)), _ when string_of_id id = "atom" ->
      Some (List.map kopt_kid kids, nc, nexp)
  | None, Typ_aux (Typ_app (id, [A_aux (A_nexp nexp, _)]), _) when string_of_id id = "atom" -> Some ([], nc_true, nexp)
  | None, Typ_aux (Typ_app (id, [A_aux (A_nexp lo, _); A_aux (A_nexp hi, _)]), l) when string_of_id id = "range" ->
      let kid = kopt_kid (named_existential l K_int name) in
      Some ([kid], nc_and (nc_lteq lo (nvar kid)) (nc_lteq (nvar kid) hi), nvar kid)
  | None, Typ_aux (Typ_id id, l) when string_of_id id = "nat" ->
      let kid = kopt_kid (named_existential l K_int name) in
      Some ([kid], nc_lteq (nint 0) (nvar kid), nvar kid)
  | None, Typ_aux (Typ_id id, l) when string_of_id id = "int" ->
      let kid = kopt_kid (named_existential l K_int name) in
      Some ([kid], nc_true, nvar kid)
  | _, _ -> None

let destruct_boolean ?name:(_ = None) = function
  | Typ_aux (Typ_id (Id_aux (Id "bool", _)), l) ->
      let kid = kopt_kid (fresh_existential l K_bool) in
      Some (kid, nc_var kid)
  | _ -> None

let destruct_exist ?(name = None) typ =
  match destruct_numeric ~name typ with
  | Some (kids, nc, nexp) -> Some (List.map (mk_kopt K_int) kids, nc, atom_typ nexp)
  | None -> (
      match destruct_boolean ~name typ with
      | Some (kid, nc) -> Some ([mk_kopt K_bool kid], nc_true, atom_bool_typ nc)
      | None -> destruct_exist_plain ~name typ
    )
