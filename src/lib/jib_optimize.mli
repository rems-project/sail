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

open Jib

(** Remove redundant assignments and variables of type
   unit. unit-typed identifiers that are assigned to are replaced with
   CL_void, and cvals (which should be pure!) are replaced with unit
   types are replaced by unit-literals. *)
val optimize_unit : instr list -> instr list

(** Remove all instructions that can contain other nested
   instructions, prodcing a flat list of instructions. *)
val flatten_instrs : instr list -> instr list

val flatten_cdef : cdef -> cdef
val reset_flat_counter : unit -> unit

val unique_per_function_ids : cdef list -> cdef list

val inline : cdef list -> (Ast.id -> bool) -> instr list -> instr list

val remove_mutrec : cdef list -> cdef list

val remove_undefined : instr list -> instr list

val remove_functions_to_references : instr list -> instr list

val remove_clear : instr list -> instr list

(** Remove gotos immediately followed by the label it jumps to *)
val remove_pointless_goto : instr list -> instr list

val remove_unused_labels : instr list -> instr list

val remove_dead_after_goto : instr list -> instr list

val remove_dead_code : instr list -> instr list

val remove_tuples : cdef list -> Jib_compile.ctx -> cdef list * Jib_compile.ctx

val structure_control_flow_block : instr list -> instr list
