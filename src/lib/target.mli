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

val run_pre_rewrites_hook : target -> tannot ast -> Effects.side_effect_info -> Env.t -> unit

val rewrites : target -> Rewrites.rewrite_sequence

val action :
  target -> Yojson.Basic.t option -> string -> string option -> tannot ast -> Effects.side_effect_info -> Env.t -> unit

val asserts_termination : target -> bool

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
   @param ?pre_rewrites_hook A function to call before doing any rewrites
   @param ?rewrites A sequence of Sail to Sail rewrite passes for the target
   @param ?asserts_termination Whether termination measures are enforced by assertions in the target

   The final unnamed parameter is the main backend function that is called after the frontend
   has finished processing the input.
 *)
val register :
  name:string ->
  ?flag:string ->
  ?description:string ->
  ?options:(Arg.key * Arg.spec * Arg.doc) list ->
  ?pre_parse_hook:(unit -> unit) ->
  ?pre_rewrites_hook:(tannot ast -> Effects.side_effect_info -> Env.t -> unit) ->
  ?rewrites:(string * Rewrites.rewriter_arg list) list ->
  ?asserts_termination:bool ->
  (Yojson.Basic.t option -> string -> string option -> tannot ast -> Effects.side_effect_info -> Env.t -> unit) ->
  target

(** Return the current target. For example, if we register a 'coq'
   target, and Sail is invoked with `sail -coq`, then this function
   will return the coq target. *)
val get_the_target : unit -> target option

val get : name:string -> target option

(** Used internally to dynamically update the option list when loading plugins *)
val extract_options : unit -> (Arg.key * Arg.spec * Arg.doc) list
