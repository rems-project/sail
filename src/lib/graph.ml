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

  val make_dot :
    node_color:(node -> string) ->
    edge_color:(node -> node -> string) ->
    string_of_node:(node -> string) ->
    out_channel ->
    graph ->
    unit
end

module Make (Ord : OrderedType) = struct
  type node = Ord.t

  (* Node set *)
  module NS = Set.Make (Ord)

  (* Node map *)
  module NM = Map.Make (Ord)

  type graph = NS.t NM.t

  type node_set = NS.t

  let empty = NM.empty

  let leaves cg =
    List.fold_left
      (fun acc (fn, callees) -> NS.filter (fun callee -> callee <> fn) (NS.union acc callees))
      NS.empty (NM.bindings cg)

  let nodes cg = NM.bindings cg |> List.map fst

  let children cg caller = try NS.elements (NM.find caller cg) with Not_found -> []

  let fix_some_leaves cg nodes =
    NS.fold (fun leaf cg -> if NM.mem leaf cg then cg else NM.add leaf NS.empty cg) nodes cg

  let fix_leaves cg = fix_some_leaves cg (leaves cg)

  let add_edge caller callee cg =
    let cg = fix_some_leaves cg (NS.singleton callee) in
    try NM.add caller (NS.add callee (NM.find caller cg)) cg with Not_found -> NM.add caller (NS.singleton callee) cg

  let add_edges caller callees cg =
    let callees = List.fold_left (fun s c -> NS.add c s) NS.empty callees in
    let cg = fix_some_leaves cg callees in
    try NM.add caller (NS.union callees (NM.find caller cg)) cg with Not_found -> NM.add caller callees cg

  let reachable roots cuts cg =
    let visited = ref NS.empty in

    let rec reachable' node =
      if NS.mem node !visited then ()
      else if NS.mem node cuts then visited := NS.add node !visited
      else begin
        visited := NS.add node !visited;
        let children = try NM.find node cg with Not_found -> NS.empty in
        NS.iter reachable' children
      end
    in

    NS.iter reachable' roots;
    !visited

  let prune roots cuts cg =
    let rs = reachable roots cuts cg in
    let cg = NM.filter (fun fn _ -> NS.mem fn rs) cg in
    let cg = NM.mapi (fun fn children -> if NS.mem fn cuts then NS.empty else children) cg in
    fix_leaves cg

  let remove_self_loops cg = NM.mapi (fun fn callees -> NS.remove fn callees) cg

  let self_loops cg = NM.fold (fun fn callees nodes -> if NS.mem fn callees then fn :: nodes else nodes) cg []

  let reverse cg =
    let rcg = ref NM.empty in
    let find_default fn cg = try NM.find fn cg with Not_found -> NS.empty in

    NM.iter
      (fun caller -> NS.iter (fun callee -> rcg := NM.add callee (NS.add caller (find_default callee !rcg)) !rcg))
      cg;
    fix_leaves !rcg

  exception Not_a_DAG of node * graph

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
      if NS.mem node !temp_marked then
        raise
          (let lcg = prune_loop node cg in
           Not_a_DAG (node, lcg)
          )
      else if NS.mem node !marked then ()
      else begin
        let children = try NM.find node cg with Not_found -> NS.empty in
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
        visit unmarked;
        topsort' ()
      with Not_found -> ()
    in

    topsort' ();
    !list

  type node_idx = { index : int; root : int }

  let scc ?(original_order : node list option) (cg : graph) =
    let components = ref [] in
    let index = ref 0 in

    let stack = ref [] in
    let push v = stack := v :: !stack in
    let pop () =
      begin
        let v = List.hd !stack in
        stack := List.tl !stack;
        v
      end
    in

    let node_indices = Hashtbl.create (NM.cardinal cg) in
    let get_index v = (Hashtbl.find node_indices v).index in
    let get_root v = (Hashtbl.find node_indices v).root in
    let set_root v r = Hashtbl.replace node_indices v { (Hashtbl.find node_indices v) with root = r } in

    let rec visit_node v =
      begin
        Hashtbl.add node_indices v { index = !index; root = !index };
        index := !index + 1;
        push v;
        if NM.mem v cg then NS.iter (visit_edge v) (NM.find v cg);
        if get_root v = get_index v then begin
          (* v is the root of a SCC *)
          let component = ref [] in
          let finished = ref false in
          while not !finished do
            let w = pop () in
            component := w :: !component;
            if Ord.compare v w = 0 then finished := true
          done;
          components := !component :: !components
        end
      end
    and visit_edge v w =
      if not (Hashtbl.mem node_indices w) then begin
        visit_node w;
        if Hashtbl.mem node_indices w then set_root v (min (get_root v) (get_root w))
      end
      else begin
        if List.mem w !stack then set_root v (min (get_root v) (get_index w))
      end
    in

    let nodes = match original_order with Some nodes -> nodes | None -> List.map fst (NM.bindings cg) in
    List.iter (fun v -> if not (Hashtbl.mem node_indices v) then visit_node v) nodes;
    List.rev !components

  let make_dot ~node_color ~edge_color ~string_of_node out_chan graph =
    Util.opt_colors := false;
    let to_string node = String.escaped (string_of_node node) in
    output_string out_chan "digraph DEPS {\n";
    let make_node from_node =
      output_string out_chan
        (Printf.sprintf "  \"%s\" [fillcolor=%s;style=filled];\n" (to_string from_node) (node_color from_node))
    in
    let make_line from_node to_node =
      output_string out_chan
        (Printf.sprintf "  \"%s\" -> \"%s\" [color=%s];\n" (to_string from_node) (to_string to_node)
           (edge_color from_node to_node)
        )
    in
    NM.bindings graph |> List.iter (fun (from_node, _) -> make_node from_node);
    NM.bindings graph |> List.iter (fun (from_node, to_nodes) -> NS.iter (make_line from_node) to_nodes);
    output_string out_chan "}\n";
    Util.opt_colors := true
end
