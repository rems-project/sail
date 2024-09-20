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

(** Infrastructure for plugins to register Sail targets.

   A {e target} is essentially a custom backend for the Sail compiler,
   along with various hooks and options that toggle various frontend
   behaviours. A target therefore specifies what kind of output Sail
   will produce. For example, we provide default plugins that define
   targets to output Lem, C, OCaml, Coq, and so on. *)

open Ast_defs
open Type_check

(** {2 Target type and accessor functions} *)

type target

val name : target -> string

val run_pre_parse_hook : target -> unit -> unit

val run_pre_initial_check_hook : target -> string list -> unit

val run_pre_rewrites_hook : target -> typed_ast -> Effects.side_effect_info -> Env.t -> unit

val rewrites : target -> Rewrites.rewrite_sequence

val action : target -> string option -> Interactive.State.istate -> unit

val asserts_termination : target -> bool

(** If a target does not support abstract types, then the user must
    provide a concrete instantiation for Sail. *)
val supports_abstract_types : target -> bool

(** {2 Target registration} *)

(** Used for plugins to register custom Sail targets/backends.

   [register_target ~name:"foo" action] will create an option -foo,
   that will run the provided action on the Sail abstract syntax tree
   after performing common frontend processing.

   The various arguments can be used to further control the
   behavior of the target:

   @param ~name The name of the target
   @param ?flag A custom command line flag to invoke the target. By default it will use the name parameter
   @param ?description A custom description for the command line flag
   @param ?options Additional options for the Sail executable
   @param ?pre_parse_hook A function to call right at the start, before parsing
   @param ?pre_initial_check_hook A function to call after parsing, but before de-sugaring
   @param ?pre_rewrites_hook A function to call before doing any rewrites
   @param ?rewrites A sequence of Sail to Sail rewrite passes for the target
   @param ?asserts_termination Whether termination measures are enforced by assertions in the target
   @param ?supports_abstract_types Whether the target supports abstract types to be passed to the target

   The final unnamed parameter is the main backend function that is called after the frontend
   has finished processing the input.
 *)
val register :
  name:string ->
  ?flag:string ->
  ?description:string ->
  ?options:(Arg.key * Arg.spec * Arg.doc) list ->
  ?pre_parse_hook:(unit -> unit) ->
  ?pre_initial_check_hook:(string list -> unit) ->
  ?pre_rewrites_hook:(typed_ast -> Effects.side_effect_info -> Env.t -> unit) ->
  ?rewrites:(string * Rewrites.rewriter_arg list) list ->
  ?asserts_termination:bool ->
  ?supports_abstract_types:bool ->
  (string option -> Interactive.State.istate -> unit) ->
  target

(** Use if you want to register a target that does nothing *)
val empty_action : string option -> Interactive.State.istate -> unit

(** Return the current target. For example, if we register a 'coq'
   target, and Sail is invoked with `sail -coq`, then this function
   will return the coq target. *)
val get_the_target : unit -> target option

val get : name:string -> target option

(** Used internally when updating the option list during plugin loading *)
val extract_registered : unit -> string list

(** Used internally to dynamically update the option list when loading plugins *)
val extract_options : unit -> (Arg.key * Arg.spec * Arg.doc) list
