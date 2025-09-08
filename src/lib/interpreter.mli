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
open Ast_defs
open Type_check
open Value_type
open Value

type gstate = {
  registers : value Bindings.t;
  allow_registers : bool; (* For some uses we want to forbid touching any registers. *)
  primops : (value list -> value) StringMap.t;
  letbinds : value Bindings.t;
  fundefs : tannot fundef Bindings.t;
  typecheck_env : Env.t;
}

module VariableUpdate : sig
  type accessor
end

type lstate = { locals : value Bindings.t }

type state = lstate * gstate

type return_value = Semantics.return_value

module Monad : sig
  type 'a t

  val pure : 'a -> 'a t
end

type frame =
  | Done of state * value
  | Step of
      string Lazy.t * state * tannot exp Monad.t * (string Lazy.t * lstate * (return_value -> tannot exp Monad.t)) list
  | Break of frame
  | Effect_request of
      string Lazy.t * state * (string Lazy.t * lstate * (return_value -> tannot exp Monad.t)) list * effect_request
  | Fail of
      string Lazy.t
      * state
      * tannot exp Monad.t
      * (string Lazy.t * lstate * (return_value -> tannot exp Monad.t)) list
      * string

and effect_request =
  | Read_reg of string * VariableUpdate.accessor list * (value -> state -> frame)
  | Write_reg of string * VariableUpdate.accessor list * value * (unit -> state -> frame)
  | Outcome of id * value list * (return_value -> tannot exp Monad.t)

val stack_string : string Lazy.t * lstate * (return_value -> tannot exp Monad.t) -> string Lazy.t

val eval_frame : frame -> frame

val default_effect_interp :
  string Lazy.t ->
  state ->
  (string Lazy.t * lstate * (return_value -> tannot exp Monad.t)) list ->
  effect_request ->
  frame

val effect_interp :
  (string Lazy.t ->
  state ->
  (string Lazy.t * lstate * (return_value -> tannot exp Monad.t)) list ->
  effect_request ->
  frame
  )
  ref

val initial_state :
  ?registers:bool -> ?undef_registers:bool -> typed_ast -> env -> (value list -> value) StringMap.t -> state
