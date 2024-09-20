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

open Ast_defs

val opt_mwords : bool ref
val opt_size_set_limit : int ref

type options = {
  auto : bool; (* Analyse ast to find splits for monomorphisation *)
  debug_analysis : int; (* Debug output level for the automatic analysis *)
  all_split_errors : bool;
  continue_anyway : bool;
}

val monomorphise :
  string ->
  (* Target backend *)
  Effects.side_effect_info ->
  options ->
  ((string * int) * string) list ->
  (* List of splits from the command line *)
  Type_check.typed_ast ->
  Type_check.typed_ast

(* Rewrite (combinations of) variable-sized operations into fixed-sized operations *)
val mono_rewrites : Type_check.typed_ast -> Type_check.typed_ast

(* Move complex nexps in function signatures into constraints *)
val rewrite_toplevel_nexps : Type_check.typed_ast -> Type_check.typed_ast

(* Move complex nexps in record fields into parameters *)
val rewrite_complete_record_params : Type_check.Env.t -> Type_check.typed_ast -> Type_check.typed_ast

(* Add casts across case splits *)
val add_bitvector_casts : Type_check.Env.t -> Type_check.typed_ast -> Type_check.typed_ast

(* Replace atom arguments which are fixed by a type parameter for a size with a singleton type *)
val rewrite_atoms_to_singletons : string -> Type_check.typed_ast -> Type_check.typed_ast
