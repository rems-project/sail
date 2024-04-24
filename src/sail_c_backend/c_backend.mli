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

open Libsail

open Ast_defs
open Jib
open Type_check

(** Global compilation options *)

(** Define generated functions as static *)
val opt_static : bool ref

(** Do not generate a main function *)
val opt_no_main : bool ref

(** (WIP) Do not include rts.h (the runtime), and do not generate code
   that requires any setup or teardown routines to be run by a runtime
   before executing any instruction semantics. *)
val opt_no_rts : bool ref

(** Do not include sail.h by default *)
val opt_no_lib : bool ref

(** Ordinarily we use plain z-encoding to name-mangle generated Sail
   identifiers into a form suitable for C. If opt_prefix is set, then
   the "z" which is added on the front of each generated C function
   will be replaced by opt_prefix. E.g. opt_prefix := "sail_" would
   give sail_my_function rather than zmy_function. *)
val opt_prefix : string ref

(** opt_extra_params and opt_extra_arguments allow additional state to
   be threaded through the generated C code by adding an additional
   parameter to each function type, and then giving an extra argument
   to each function call. For example we could have

   opt_extra_params := Some "CPUMIPSState *env"
   opt_extra_arguments := Some "env"

   and every generated function will take a pointer to a QEMU MIPS
   processor state, and each function will be passed the env argument
   when it is called. *)
val opt_extra_params : string option ref

val opt_extra_arguments : string option ref

val opt_branch_coverage : out_channel option ref

(** Optimization flags *)

val optimize_primops : bool ref
val optimize_hoist_allocations : bool ref
val optimize_struct_updates : bool ref
val optimize_alias : bool ref
val optimize_fixed_int : bool ref
val optimize_fixed_bits : bool ref

val jib_of_ast : Env.t -> Effects.side_effect_info -> tannot ast -> cdef list * Jib_compile.ctx
val compile_ast : Env.t -> Effects.side_effect_info -> out_channel -> string list -> tannot ast -> unit

val compile_ast_clib : Env.t -> Effects.side_effect_info -> tannot ast -> (Jib_compile.ctx -> cdef list -> unit) -> unit
