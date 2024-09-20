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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

(** Type error utilities

This file wraps the functions in Type_check, so they return
Fatal_error exceptions from the Reporting module rather than
Type_errors. *)

open Ast
open Ast_util
open Type_env

(** If false (default), we'll only explain generated variables, not
   variables written explicitly by the user in the source. *)
val opt_explain_all_variables : bool ref

(** If false (default), we'll list relevant constraints, but not go
   into detail about how they were derived *)
val opt_explain_constraints : bool ref

(** If false (default), we will try to pick the most likely error to
    have caused an overload to fail, and only show those. If true, we
    will show all type errors that caused an overload to fail. *)
val opt_explain_all_overloads : bool ref

type constraint_reason = (l * string) option

type type_error =
  | Err_no_overloading of id * (id * Parse_ast.l * type_error) list
  | Err_unresolved_quants of id * quant_item list * (mut * typ) Bindings.t * type_variables * n_constraint list
  | Err_failed_constraint of n_constraint * (mut * typ) Bindings.t * type_variables * n_constraint list
  | Err_subtype of typ * typ * n_constraint option * (constraint_reason * n_constraint) list * type_variables
  | Err_no_num_ident of id
  | Err_other of string
  | Err_inner of type_error * Parse_ast.l * string * type_error
  | Err_not_in_scope of
      string option * Parse_ast.l option * string Project.spanned option * string Project.spanned option * bool
  | Err_instantiation_info of int * type_error
  | Err_function_arg of Parse_ast.l * typ * type_error
  | Err_no_function_type of { id : id; functions : (typquant * typ) Bindings.t }
      (** Takes the name of the function and the set of functions in scope *)
  | Err_unbound_id of { id : id; locals : (mut * typ) Bindings.t; have_function : bool }
      (** Takes the name of the identifier, the set of local bindings, and
          whether we have a function of the same name in scope. *)
  | Err_hint of string  (** A short error that only appears attached to a location *)
  | Err_with_hint of string * type_error

exception Type_error of Parse_ast.l * type_error

type suggestion = Suggest_add_constraint of Ast.n_constraint | Suggest_none

(** Analyze an unresolved quantifier type error *)
val analyze_unresolved_quant :
  (Ast_util.mut * Ast.typ) Ast_util.Bindings.t -> Ast.n_constraint list -> Ast.quant_item -> suggestion

val string_of_type_error : type_error -> string * string option

(** Convert a type error into a general purpose error from the Reporting file *)
val to_reporting_exn : Parse_ast.l -> type_error -> exn

val check_defs : Type_check.Env.t -> untyped_def list -> Type_check.typed_def list * Type_check.Env.t

val check : Type_check.Env.t -> untyped_ast -> Type_check.typed_ast * Type_check.Env.t
