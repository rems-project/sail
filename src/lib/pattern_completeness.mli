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

open Ast
open Ast_util

(** For testing, we don't want our tests to print exact literals in
    warnings, otherwise they would be overly brittle. This is because
    we use an SMT solver to find counterexamples to complex
    constrained patterns, and it's not guaranteed to find the same one
    each run, or between different versions of the solver. *)
val opt_debug_no_literals : bool ref

type ctx = {
  variants : (typquant * type_union list) Bindings.t;
  structs : (typquant * (typ * id) list) Bindings.t;
  enums : IdSet.t Bindings.t;
  constraints : n_constraint list;
  is_mapping : id -> bool;
}

module type Config = sig
  type t
  val typ_of_t : t -> typ
  val add_attribute : l -> string -> attribute_data option -> t -> t
end

module Make (C : Config) : sig
  val is_complete_wildcarded : ?keyword:string -> Parse_ast.l -> ctx -> C.t pexp list -> typ -> C.t pexp list option
  val is_complete_funcls_wildcarded :
    ?keyword:string -> Parse_ast.l -> ctx -> C.t funcl list -> typ -> C.t funcl list option
  val is_complete : ?keyword:string -> Parse_ast.l -> ctx -> C.t pexp list -> typ -> bool
  val is_complete_mapcls_wildcarded : ?keyword:string -> Parse_ast.l -> ctx -> C.t mapcl list -> typ -> typ -> bool
end
