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

(** Functions for generating and interacting with Sail call graphs. *)

open Ast
open Ast_defs
open Ast_util

type node =
  | Register of id
  | Function of id
  | Mapping of id
  | Letbind of id
  | Type of id
  | Overload of id
  | Constructor of id
  | FunctionMeasure of id
  | LoopMeasures of id
  | Outcome of id

val node_id : node -> id

module Node : sig
  type t = node
  val compare : node -> node -> int
end

module NodeSet : sig
  include Set.S with type elt = node and type t = Set.Make(Node).t
end

module NodeMap : sig
  include Map.S with type key = node and type 'a t = 'a Map.Make(Node).t
end

module G : sig
  include Graph.S with type node = Node.t and type node_set = Set.Make(Node).t and type graph = Graph.Make(Node).graph
end

type callgraph = G.graph

val graph_of_ast : Type_check.typed_ast -> callgraph

val nodes_of_def : ('a, 'b) def -> NodeSet.t

val filter_ast_ids : IdSet.t -> IdSet.t -> Type_check.typed_ast -> Type_check.typed_ast

val filter_ast : Set.Make(Node).t -> callgraph -> ('a, 'b) ast -> ('a, 'b) ast

val filter_ast_extra : Set.Make(Node).t -> callgraph -> ('a, 'b) ast -> bool -> ('a, 'b) ast

val top_sort_defs : Type_check.typed_ast -> Type_check.typed_ast

val slice_instantiation_types : string -> Type_check.typed_ast -> Type_check.typed_ast
