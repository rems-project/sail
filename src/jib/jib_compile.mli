(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

(** Compile Sail ASTs to Jib intermediate representation *)

open Anf
open Ast
open Ast_util
open Jib
open Type_check

(** Output a dataflow graph for each generated function in Graphviz
   (dot) format. *)
val opt_debug_flow_graphs : bool ref

(** Print the IR representation of a specific function. *)
val opt_debug_function : string ref

val ngensym : unit -> name

(** {2 Jib context} *)

(** Context for compiling Sail to Jib. We need to pass a (global)
   typechecking environment given by checking the full AST. We have to
   provide a conversion function from Sail types into Jib types, as
   well as a function that optimizes ANF expressions (which can just
   be the identity function) *)
type ctx =
  { records : (ctyp Bindings.t) Bindings.t;
    enums : IdSet.t Bindings.t;
    variants : (ctyp Bindings.t) Bindings.t;
    tc_env : Env.t;
    local_env : Env.t;
    locals : (mut * ctyp) Bindings.t;
    letbinds : int list;
    no_raw : bool;
    convert_typ : ctx -> typ -> ctyp;
    optimize_anf : ctx -> typ aexp -> typ aexp;
    specialize_calls : bool;
    ignore_64 : bool
  }

val initial_ctx :
  convert_typ:(ctx -> typ -> ctyp) ->
  optimize_anf:(ctx -> typ aexp -> typ aexp) ->
  Env.t ->
  ctx

(** {2 Compilation functions} *)

(** Compile a Sail definition into a Jib definition. The first two
   arguments are is the current definition number and the total number
   of definitions, and can be used to drive a progress bar (see
   Util.progress). *)
val compile_def : int -> int -> ctx -> tannot def -> cdef list * ctx

val compile_ast : ctx -> tannot defs -> cdef list * ctx
