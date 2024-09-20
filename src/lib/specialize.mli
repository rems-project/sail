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

(** Rewrites for removing polymorphism from specifications *)

open Ast
open Ast_defs
open Ast_util
open Type_check

val opt_ddump_spec_ast : (string * int) option ref

type specialization

(** Only specialize Type- kinded polymorphism. *)
val typ_specialization : specialization

(** (experimental) specialise Int-kinded definitions *)
val int_specialization : specialization

(** (experimental) specialise Int-kinded definitions, including externs *)
val int_specialization_with_externs : specialization

(** Returns an IdSet with the function ids that have X-kinded
   parameters, e.g. val f : forall ('a : X). 'a -> 'a. The first
   argument specifies what X should be - it should be one of:
   [is_int_kopt], [is_order_kopt], or [is_typ_kopt] from [Ast_util],
   or some combination of those. *)
val polymorphic_functions : specialization -> ('a, 'b) def list -> IdSet.t

val add_initial_calls : IdSet.t -> unit

val get_initial_calls : unit -> id list

(** specialize returns an AST with all the Order and Type polymorphism
   removed, as well as the environment produced by type checking that
   AST with [Type_check.initial_env]. The env parameter is the
   environment to return if there is no polymorphism to remove, in
   which case specialize returns the AST unmodified. *)
val specialize :
  specialization -> Env.t -> typed_ast -> Effects.side_effect_info -> typed_ast * Env.t * Effects.side_effect_info

(** specialize' n performs at most n specialization passes. Useful for
   int_specialization which is not guaranteed to terminate. *)
val specialize_passes :
  int ->
  specialization ->
  Env.t ->
  typed_ast ->
  Effects.side_effect_info ->
  typed_ast * Env.t * Effects.side_effect_info

(** return all instantiations of a function id, with the
   instantiations filtered according to the specialization. *)
val instantiations_of : specialization -> id -> typed_ast -> typ_arg KBindings.t list

val string_of_instantiation : typ_arg KBindings.t -> string
