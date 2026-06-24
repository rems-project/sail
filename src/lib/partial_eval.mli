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

(** This module provides an interface to the Rocq [Extraction.ZAst] module for partial evaluation of Sail expressions.
*)

open Ast

type gstate

val initial_gstate : typecheck_env:Type_check.Env.t -> ast:Type_check.typed_ast -> gstate

module Zinterp : sig
  type t

  module R : sig
    module L : sig
      type t
    end

    type value = { this : L.t option; exn : L.t option; eff : bool }
  end
end

module Pretty : sig
  val string_of_value : Zinterp.R.L.t -> string

  val docs : Zinterp.t -> PPrint.document list
end

type partial_state

val from_exp : Type_check.tannot exp -> partial_state

(** Wrap the user expression in the program's top-level [let] bindings before starting partial evaluation, so global
    identifiers are in scope. *)
val from_exp_with_globals : gstate -> Type_check.tannot exp -> partial_state

val partial_state_ctx : partial_state -> Zinterp.t

val string_of_focus : partial_state -> string

val is_finished : partial_state -> Zinterp.R.value option

val mk_interpreter : inlining:bool -> gstate -> partial_state -> partial_state
