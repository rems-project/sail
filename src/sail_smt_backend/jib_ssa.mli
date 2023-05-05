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

open Array
open Jib_util

(** A mutable array based graph type, with nodes indexed by integers. *)
type 'a array_graph

(** Create an empty array_graph, specifying the initial size of the
   underlying array. *)
val make : initial_size:int -> unit -> 'a array_graph

module IntSet : Set.S with type elt = int

val get_cond : 'a array_graph -> int -> Jib.cval

val get_vertex : 'a array_graph -> int -> ('a * IntSet.t * IntSet.t) option

val iter_graph : ('a -> IntSet.t -> IntSet.t -> unit) -> 'a array_graph -> unit

(** Add a vertex to a graph, returning the index of the inserted
   vertex. If the number of vertices exceeds the size of the
   underlying array, then it is dynamically resized. *)
val add_vertex : 'a -> 'a array_graph -> int

(** Add an edge between two existing vertices. Raises Invalid_argument
   if either of the vertices do not exist. *)
val add_edge : int -> int -> 'a array_graph -> unit

exception Not_a_DAG of int

val topsort : 'a array_graph -> int list

type terminator =
  | T_undefined of Jib.ctyp
  | T_exit of string
  | T_end of Jib.name
  | T_goto of string
  | T_jump of int * string
  | T_label of string
  | T_none

type cf_node =
  | CF_label of string
  | CF_block of Jib.instr list * terminator
  | CF_guard of int
  | CF_start of Jib.ctyp NameMap.t

val control_flow_graph : Jib.instr list -> int * int list * ('a list * cf_node) array_graph

(** [immediate_dominators graph root] will calculate the immediate
   dominators for a control flow graph with a specified root node. *)
val immediate_dominators : 'a array_graph -> int -> int array

type ssa_elem = Phi of Jib.name * Jib.ctyp * Jib.name list | Pi of Jib.cval list

(** Convert a list of instructions into SSA form *)
val ssa : Jib.instr list -> int * (ssa_elem list * cf_node) array_graph

(** Output the control-flow graph in graphviz format for
   debugging. Can use 'dot -Tpng X.gv -o X.png' to generate a png
   image of the graph. *)
val make_dot : out_channel -> (ssa_elem list * cf_node) array_graph -> unit

val make_dominators_dot : out_channel -> int array -> (ssa_elem list * cf_node) array_graph -> unit
