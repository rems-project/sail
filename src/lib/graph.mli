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

(** Generic graph type based on OCaml Set and Map *)

module type OrderedType = sig
  type t
  val compare : t -> t -> int
end

module type S = sig
  type node
  type graph
  type node_set

  val leaves : graph -> node_set

  val empty : graph

  (** Add an edge from the first node to the second node, creating
       the nodes if they do not exist. *)
  val add_edge : node -> node -> graph -> graph

  val has_edge : node -> node -> graph -> bool

  val delete_edge : node -> node -> graph -> graph

  val add_edges : node -> node list -> graph -> graph

  val children : graph -> node -> node list

  val nodes : graph -> node list

  (** Return the set of nodes that are reachable from the first set
       of nodes (roots), without passing through the second set of
       nodes (cuts). *)
  val reachable : node_set -> node_set -> graph -> node_set

  (** Prune a graph from roots to cuts. *)
  val prune : node_set -> node_set -> graph -> graph

  val remove_self_loops : graph -> graph

  val self_loops : graph -> node list

  val reverse : graph -> graph

  exception Not_a_DAG of node * graph

  (** Topologically sort a graph. Throws Not_a_DAG if the graph is
       not directed acyclic. *)
  val topsort : graph -> node list

  (** Find strongly connected components using Tarjan's algorithm.
        This algorithm also returns a topological sorting of the graph
        components. *)
  val scc : ?original_order:node list -> graph -> node list list

  val edge_list : graph -> (node * node) list

  (** Note that this is at least O(n^3) where n is the number of nodes
      and very inefficiently constructs the result graph! *)
  val transitive_reduction : graph -> graph

  val make_multi_dot :
    node_color:(node -> string) ->
    edge_color:(node -> node -> string) ->
    string_of_node:(node -> string) ->
    out_channel ->
    (string * graph) list ->
    unit

  val make_dot :
    node_color:(node -> string) ->
    edge_color:(node -> node -> string) ->
    string_of_node:(node -> string) ->
    out_channel ->
    graph ->
    unit
end

module Make (Ord : OrderedType) :
  S with type node = Ord.t and type node_set = Set.Make(Ord).t and type graph = Set.Make(Ord).t Map.Make(Ord).t
