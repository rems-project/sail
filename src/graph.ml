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

module type OrderedType =
  sig
    type t
    val compare : t -> t -> int
  end

module type S =
  sig
    type node
    type graph
    type node_set

    val leaves : graph -> node_set

    val empty : graph

    (** Add an edge from the first node to the second node, creating
       the nodes if they do not exist. *)
    val add_edge : node -> node -> graph -> graph
    val add_edges : node -> node list -> graph -> graph

    val children : graph -> node -> node list

    (** Return the set of nodes that are reachable from the first set
       of nodes (roots), without passing through the second set of
       nodes (cuts). *)
    val reachable : node_set -> node_set -> graph -> node_set

    (** Prune a graph from roots to cuts. *)
    val prune : node_set -> node_set -> graph -> graph

    val remove_self_loops : graph -> graph

    val reverse : graph -> graph

    exception Not_a_DAG of node * graph;;

    (** Topologically sort a graph. Throws Not_a_DAG if the graph is
       not directed acyclic. *)
    val topsort : graph -> node list
  end

module Make(Ord: OrderedType) = struct

  type node = Ord.t

  (* Node set *)
  module NS = Set.Make(Ord)
  (* Node map *)
  module NM = Map.Make(Ord)

  type graph = NS.t NM.t

  type node_set = NS.t

  let empty = NM.empty

  let leaves cg =
    List.fold_left (fun acc (fn, callees) -> NS.filter (fun callee -> callee <> fn) (NS.union acc callees)) NS.empty (NM.bindings cg)

  let children cg caller =
    try
      NS.elements (NM.find caller cg)
    with
    | Not_found -> []

  let fix_leaves cg =
    NS.fold (fun leaf cg -> if NM.mem leaf cg then cg else NM.add leaf NS.empty cg) (leaves cg) cg

  (* FIXME: don't use fix_leaves because this is inefficient *)
  let add_edge caller callee cg =
    try
      fix_leaves (NM.add caller (NS.add callee (NM.find caller cg)) cg)
    with
    | Not_found -> fix_leaves (NM.add caller (NS.singleton callee) cg)

  let add_edges caller callees cg =
    let callees = List.fold_left (fun s c -> NS.add c s) NS.empty callees in
    try
      fix_leaves (NM.add caller (NS.union callees (NM.find caller cg)) cg)
    with
    | Not_found -> fix_leaves (NM.add caller callees cg)

  let reachable roots cuts cg =
    let visited = ref NS.empty in

    let rec reachable' node =
      if NS.mem node !visited then ()
      else if NS.mem node cuts then visited := NS.add node !visited
      else
        begin
          visited := NS.add node !visited;
          let children =
            try NM.find node cg with
            | Not_found -> NS.empty
          in
          NS.iter reachable' children
        end
    in

    NS.iter reachable' roots; !visited

  let prune roots cuts cg =
    let rs = reachable roots cuts cg in
    fix_leaves (NM.filter (fun fn _ -> NS.mem fn rs) cg)

  let remove_self_loops cg =
    NM.mapi (fun fn callees -> NS.remove fn callees) cg

  let reverse cg =
    let rcg = ref NM.empty in
    let find_default fn cg = try NM.find fn cg with Not_found -> NS.empty in

    NM.iter (fun caller -> NS.iter (fun callee -> rcg := NM.add callee (NS.add caller (find_default callee !rcg)) !rcg)) cg;
    fix_leaves !rcg

  exception Not_a_DAG of node * graph;;

  let prune_loop node cg =
    let down = prune (NS.singleton node) NS.empty cg in
    let up = prune (NS.singleton node) NS.empty (reverse down) in
    reverse up

  let topsort cg =
    let marked = ref NS.empty in
    let temp_marked = ref NS.empty in
    let list = ref [] in
    let keys = NM.bindings cg |> List.map fst in
    let find_unmarked keys = List.find (fun node -> not (NS.mem node !marked)) keys in

    let rec visit node =
      if NS.mem node !temp_marked
      then raise (let lcg = prune_loop node cg in Not_a_DAG (node, lcg))
      else if NS.mem node !marked
      then ()
      else
        begin
          let children =
            try NM.find node cg with
            | Not_found -> NS.empty
          in
          temp_marked := NS.add node !temp_marked;
          NS.iter (fun child -> visit child) children;
          marked := NS.add node !marked;
          temp_marked := NS.remove node !temp_marked;
          list := node :: !list
        end
    in

    let rec topsort' () =
      try
        let unmarked = find_unmarked keys in
        visit unmarked; topsort' ()
      with
      | Not_found -> ()

    in topsort' (); !list

end
