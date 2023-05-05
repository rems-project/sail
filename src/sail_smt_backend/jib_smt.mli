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

open Ast
open Ast_defs
open Ast_util
open Jib
open Jib_util
open Jib_ssa
open Smtlib

val opt_ignore_overflow : bool ref
val opt_auto : bool ref
val opt_debug_graphs : bool ref
val opt_propagate_vars : bool ref

val zencode_name : name -> string

module IntSet : Set.S with type elt = int
module EventMap : Map.S with type key = Property.event

(** These give the default bounds for various SMT types, stored in the
   initial_ctx. *)

val opt_default_lint_size : int ref
val opt_default_lbits_index : int ref
val opt_default_vector_index : int ref

type ctx = {
  lbits_index : int;
      (** Arbitrary-precision bitvectors are represented as a (BitVec lbits_index, BitVec (2 ^ lbits_index)) pair. *)
  lint_size : int;  (** The size we use for integers where we don't know how large they are statically. *)
  vector_index : int;
      (** A generic vector, vector('a) becomes Array (BitVec vector_index) 'a.
       We need to take care that vector_index is large enough for all generic vectors. *)
  register_map : id list CTMap.t;  (** A map from each ctyp to a list of registers of that ctyp *)
  tuple_sizes : IntSet.t ref;  (** A set to keep track of all the tuple sizes we need to generate types for *)
  tc_env : Type_check.Env.t;  (** tc_env is the global type-checking environment *)
  pragma_l : Ast.l;
      (** A location, usually the $counterexample or $property we are
       generating the SMT for. Used for error messages. *)
  arg_stack : (int * string) Stack.t;  (** Used internally to keep track of function argument names *)
  ast : Type_check.tannot ast;  (** The fully type-checked ast *)
  shared : ctyp Bindings.t;
      (** Shared variables. These variables do not get renamed by
       Smtlib.suffix_variables_def, and their SSA number is
       omitted. They should therefore only ever be read and never
       written. Used by sail-axiomatic for symbolic values in the
       initial litmus state. *)
  preserved : IdSet.t;
      (** icopy instructions to an id in preserved will generated a
       define-const (by using Smtlib.Preserved_const) that will not be
       simplified away or renamed. It will also not get a SSA
       number. Such variables can therefore only ever be written to
       once, and never read. They are used by sail-axiomatic to
       extract information from the generated SMT. *)
  events : smt_exp Stack.t EventMap.t ref;
      (** For every event type we have a stack of boolean SMT
       expressions for each occurance of that event. See
       src/property.ml for the event types *)
  node : int;
  pathcond : smt_exp Lazy.t;
      (** When generating SMT for an instruction pathcond will contain
       the global path conditional of the containing block/node in the
       control flow graph *)
  use_string : bool ref;
  use_real : bool ref;
      (** Set if we need to use strings or real numbers in the generated
       SMT, which then requires set-logic ALL or similar depending on
       the solver *)
}

(** Compile an AST into Jib suitable for SMT generation, and initialise a context. *)
val compile : Type_check.Env.t -> Effects.side_effect_info -> Type_check.tannot ast -> cdef list * Jib_compile.ctx * ctx

(* TODO: Currently we internally use mutable stacks and queues to
   avoid any issues with stack overflows caused by some non
   tail-recursive list functions, as the generated SMT can be very
   long, especially without any optimization. Not clear that this is
   really better than just using lists. *)

val smt_header : ctx -> cdef list -> smt_def list

val smt_query : ctx -> Property.query -> smt_exp

val smt_instr_list :
  string -> ctx -> cdef list -> instr list -> smt_def Stack.t * int * (ssa_elem list * cf_node) Jib_ssa.array_graph

module type Sequence = sig
  type 'a t
  val create : unit -> 'a t
  val add : 'a -> 'a t -> unit
end

(** Optimize SMT generated by smt_instr_list. SMT definitions are
   added to the result sequence in the order they should appear in the
   final SMTLIB file. Depending on the order in which we want to
   process the results we can either use a FIFO queue or a LIFO
   stack, or any other structure. *)
module Make_optimizer (S : Sequence) : sig
  val optimize : smt_def Stack.t -> smt_def S.t
end

val serialize_smt_model : string -> Type_check.Env.t -> Effects.side_effect_info -> Type_check.tannot ast -> unit

val deserialize_smt_model : string -> cdef list * ctx

(** Generate SMT for all the $property and $counterexample pragmas in
   an AST, and write it to appropriately named files. *)
val generate_smt :
  (string * string * l * 'a val_spec) Bindings.t (* See Property.find_properties *) ->
  (string -> string) ->
  (* Applied to each function name to generate the file name for the smtlib file *)
  Type_check.Env.t ->
  Effects.side_effect_info ->
  Type_check.tannot ast ->
  unit
