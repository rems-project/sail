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

open Ast
open Ast_util
open Jib
open Jib_util
open Smtlib

val opt_ignore_overflow : bool ref
val opt_auto : bool ref
val opt_debug_graphs : bool ref
val opt_propagate_vars : bool ref

module IntSet : Set.S with type elt = int
module EventMap : Map.S with type key = Property.event

val opt_default_lint_size : int ref
val opt_default_lbits_index : int ref
val opt_default_vector_index : int ref

type ctx = {
    (** Arbitrary-precision bitvectors are represented as a (BitVec lbits_index, BitVec (2 ^ lbits_index)) pair. *)
    lbits_index : int;
    (** The size we use for integers where we don't know how large they are statically. *)
    lint_size : int;
    (** A generic vector, vector('a) becomes Array (BitVec vector_index) 'a.
       We need to take care that vector_index is large enough for all generic vectors. *)
    vector_index : int;
    (** A map from each ctyp to a list of registers of that ctyp *)
    register_map : id list CTMap.t;
    (** A set to keep track of all the tuple sizes we need to generate types for *)
    tuple_sizes : IntSet.t ref;
    (** tc_env is the global type-checking environment *)
    tc_env : Type_check.Env.t;
    (** A location, usually the $counterexample or $property we are
       generating the SMT for. Used for error messages. *)
    pragma_l : Ast.l;
    (** Used internally to keep track of function argument names *)
    arg_stack : (int * string) Stack.t;
    (** The fully type-checked ast *)
    ast : Type_check.tannot defs;
    (** For every event type we have a stack of boolean SMT
       expressions for each occurance of that event. See
       src/property.ml for the event types *)
    events : smt_exp Stack.t EventMap.t ref;
    (** When generating SMT for an instruction pathcond will contain
       the global path conditional of the containing block in the
       control flow graph *)
    pathcond : smt_exp Lazy.t;
    (** Set if we need to use strings or real numbers in the generated
       SMT, which then requires set-logic ALL or similar depending on
       the solver *)
    use_string : bool ref;
    use_real : bool ref
  }

val smt_instr_list : string -> ctx -> cdef list -> instr list -> smt_def Stack.t

(** Generate SMT for all the $property and $counterexample pragmas in an AST *)
val generate_smt :
  (string * string * l * 'a val_spec) Bindings.t
  -> (string -> string)
  -> Type_check.Env.t
  -> Type_check.tannot defs
  -> unit
