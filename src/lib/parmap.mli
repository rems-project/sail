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
(*  Copyright (c) 2013-2026                                                 *)
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

(** This module provides a parallel map function that uses OCaml 5 Effect handlers to provide a limited form of
    parallelism.

    Functions called underneath [map] or [toplevel_handler] can use the functions in the [ParUnix] module to open
    subprocesses which will, in the case of [map], will be ran in parallel as the [map] implementation continues to
    apply the provided function to subsequent elements of the list (which may themselves invoke subprocesses, up to the
    [parallism] limit, at which point the map function will wait).

    The [toplevel_handler] does not provide any parallism, but is instead wrapped around the main function as a global
    handler to catch any uses of the [ParUnix] functions that do not occur underneath a [map].

    This is intended for parts of Sail that make heavy use of the SMT solver, because it allows us to do things like
    e.g. process function bodies in parallel. *)

(** When true, makes [map] behave exactly as [List.map]. Useful for debugging and testing, as it makes the output fully
    deterministic. Default [false]. *)
val opt_sequential : bool ref

module ParUnix : sig
  val open_process_full : string -> string Array.t -> string option -> Unix.process_status * string * string
end

(** Always returns a value greater than or equal to 1. *)
val recommended_parallelism : unit -> int

val map : parallelism:int -> ('a -> 'b) -> 'a list -> 'b list

val toplevel_handler : (unit -> 'a) -> 'a
