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

open Ast_util
open Jib
open Jib_util

module IntSet = Set.Make(struct type t = int let compare = compare end)

(**************************************************************************)
(* 1. Mutable graph type                                                  *)
(**************************************************************************)

type 'a array_graph = {
    mutable next : int;
    mutable nodes : ('a * IntSet.t * IntSet.t) option array
  }

let make ~initial_size () = {
    next = 0;
    nodes = Array.make initial_size None
  }

(** Add a vertex to a graph, returning the node index *)
let add_vertex data graph =
  let n = graph.next in
  if n >= Array.length graph.nodes then
    begin
      let new_nodes = Array.make (Array.length graph.nodes * 2) None in
      Array.blit graph.nodes 0 new_nodes 0 (Array.length graph.nodes);
      graph.nodes <- new_nodes
    end;
  let n = graph.next in
  graph.nodes.(n) <- Some (data, IntSet.empty, IntSet.empty);
  graph.next <- n + 1;
  n

(** Add an edge between two existing vertices. Raises Invalid_argument
   if either of the vertices do not exist. *)
let add_edge n m graph =
  begin match graph.nodes.(n) with
  | Some (data, parents, children) ->
     graph.nodes.(n) <- Some (data, parents, IntSet.add m children)
  | None ->
     raise (Invalid_argument "Parent node does not exist in graph")
  end;
  match graph.nodes.(m) with
  | Some (data, parents, children) ->
     graph.nodes.(m) <- Some (data, IntSet.add n parents, children)
  | None ->
     raise (Invalid_argument "Child node does not exist in graph")

let cardinal graph = graph.next

let reachable roots graph =
  let visited = ref IntSet.empty in

  let rec reachable' n =
    if IntSet.mem n !visited then ()
    else
      begin
        visited := IntSet.add n !visited;
        match graph.nodes.(n) with
        | Some (_, _, successors) ->
           IntSet.iter reachable' successors
        | None -> ()
      end
  in
  IntSet.iter reachable' roots; !visited

let prune visited graph =
  for i = 0 to graph.next - 1 do
    match graph.nodes.(i) with
    | Some (n, preds, succs) ->
       if IntSet.mem i visited then
         graph.nodes.(i) <- Some (n, IntSet.inter visited preds, IntSet.inter visited succs)
       else
         graph.nodes.(i) <- None
    | None -> ()
  done

(**************************************************************************)
(* 2. Mutable control flow graph                                          *)
(**************************************************************************)

type cf_node =
  | CF_label of string
  | CF_block of instr list
  | CF_start

let control_flow_graph instrs =
  let module StringMap = Map.Make(String) in
  let labels = ref StringMap.empty in

  let graph = make ~initial_size:512 () in

  iter_instr (fun (I_aux (instr, annot)) ->
      match instr with
      | I_label label ->
         labels := StringMap.add label (add_vertex ([], CF_label label) graph) !labels
      | _ -> ()
    ) (iblock instrs);

  let cf_split (I_aux (aux, _)) =
    match aux with
    | I_block _ | I_label _ | I_goto _ | I_jump _ | I_if _ | I_end | I_match_failure | I_undefined _ -> true
    | _ -> false
  in

  let rec cfg preds instrs =
    let before, after = instr_split_at cf_split instrs in
    let last = match after with
      | I_aux (I_label _, _) :: _ -> []
      | instr :: _ -> [instr]
      | _ -> []
    in
    let preds = match before @ last with
      | [] -> preds
      | instrs ->
         let n = add_vertex ([], CF_block instrs) graph in
         List.iter (fun p -> add_edge p n graph) preds;
         [n]
    in
    match after with
    | I_aux (I_if (cond, then_instrs, else_instrs, _), _) :: after ->
       let t = cfg preds then_instrs in
       let e = cfg preds else_instrs in
       cfg (t @ e) after

    | I_aux ((I_end | I_match_failure | I_undefined _), _) :: after ->
       cfg [] after

    | I_aux (I_goto label, _) :: after ->
       List.iter (fun p -> add_edge p (StringMap.find label !labels) graph) preds;
       cfg [] after

    | I_aux (I_jump (cval, label), _) :: after ->
       List.iter (fun p -> add_edge p (StringMap.find label !labels) graph) preds;
       cfg preds after

    | I_aux (I_label label, _) :: after ->
       cfg (StringMap.find label !labels :: preds) after

    | I_aux (I_block instrs, _) :: after ->
       let m = cfg preds instrs in
       cfg m after

    | _ :: after -> assert false

    | [] -> preds
  in

  let start = add_vertex ([], CF_start) graph in
  let finish = cfg [start] instrs in

  let visited = reachable (IntSet.singleton start) graph in
  prune visited graph;

  start, finish, graph

(**************************************************************************)
(* 3. Computing dominators                                                *)
(**************************************************************************)

(** Calculate the (immediate) dominators of a graph using the
   Lengauer-Tarjan algorithm. This is the slightly less sophisticated
   version from Appel's book 'Modern compiler implementation in ML'
   which runs in O(n log(n)) time. *)
let immediate_dominators graph root =
  let none = -1 in
  let vertex   = Array.make (cardinal graph) 0 in
  let parent   = Array.make (cardinal graph) none in
  let ancestor = Array.make (cardinal graph) none in
  let semi     = Array.make (cardinal graph) none in
  let idom     = Array.make (cardinal graph) none in
  let samedom  = Array.make (cardinal graph) none in
  let best     = Array.make (cardinal graph) none in
  let dfnum    = Array.make (cardinal graph) 0 in
  let bucket   = Array.make (cardinal graph) IntSet.empty in

  let rec ancestor_with_lowest_semi v =
    let a = ancestor.(v) in
    if ancestor.(a) <> none then
      let b = ancestor_with_lowest_semi a in
      ancestor.(v) <- ancestor.(a);
      if dfnum.(semi.(b)) < dfnum.(semi.(best.(v))) then
        best.(v) <- b
      else ();
    else ();
    if best.(v) <> none then best.(v) else v
  in

  let link p n =
    ancestor.(n) <- p;
    best.(n) <- n
  in

  let count = ref 0 in

  let rec dfs p n =
    if dfnum.(n) = 0 then
      begin
        dfnum.(n) <- !count;
        vertex.(!count) <- n;
        parent.(n) <- p;
        incr count;
        match graph.nodes.(n) with
        | Some (_, _, successors) ->
           IntSet.iter (fun w -> dfs n w) successors
        | None -> assert false
      end
  in
  dfs none root;

  for i = !count - 1 downto 1 do
    let n = vertex.(i) in
    let p = parent.(n) in
    let s = ref p in

    begin match graph.nodes.(n) with
    | Some (_, predecessors, _) ->
       IntSet.iter (fun v ->
           let s' =
             if dfnum.(v) <= dfnum.(n) then
               v
             else
               semi.(ancestor_with_lowest_semi v)
           in
           if dfnum.(s') < dfnum.(!s) then s := s'
         ) predecessors
    | None -> assert false
    end;
    semi.(n) <- !s;
    bucket.(!s) <- IntSet.add n bucket.(!s);
    link p n;
    IntSet.iter (fun v ->
        let y = ancestor_with_lowest_semi v in
        if semi.(y) = semi.(v) then
          idom.(v) <- p
        else
          samedom.(n) <- y
      ) bucket.(p);
  done;
  for i = 1 to !count - 1 do
    let n = vertex.(i) in
    if samedom.(n) <> none then
      idom.(n) <- idom.(samedom.(n))
  done;
  idom

(** [(dominator_children idoms).(n)] are the nodes whose immediate dominator
   (idom) is n. *)
let dominator_children idom =
  let none = -1 in
  let children = Array.make (Array.length idom) IntSet.empty in

  for n = 0 to Array.length idom - 1 do
    let p = idom.(n) in
    if p <> none then
      children.(p) <- IntSet.add n (children.(p))
  done;
  children

(** [dominate idom n w] is true if n dominates w in the tree of
   immediate dominators idom. *)
let rec dominate idom n w =
  let none = -1 in
  let p = idom.(n) in
  if p = none then
    false
  else if p = w then
    true
  else
    dominate idom p w

let dominance_frontiers graph root idom children =
  let df = Array.make (cardinal graph) IntSet.empty in

  let rec compute_df n =
    let set = ref IntSet.empty in

    begin match graph.nodes.(n) with
    | Some (content, _, succs) ->
       IntSet.iter (fun y ->
           if idom.(y) <> n then
             set := IntSet.add y !set
         ) succs
    | None -> ()
    end;
    IntSet.iter (fun c ->
        compute_df c;
        IntSet.iter (fun w ->
            if not (dominate idom n w) then
              set := IntSet.add w !set
          ) (df.(c))
      ) (children.(n));
    df.(n) <- !set
  in
  compute_df root;
  df

(**************************************************************************)
(* 4. Conversion to SSA form                                              *)
(**************************************************************************)

type ssa_elem =
  | Phi of Ast.id * Ast.id list

let place_phi_functions graph df =
  let defsites = ref Bindings.empty in

  let all_vars = ref IdSet.empty in

  let rec all_decls = function
    | I_aux (I_decl (_, id), _) :: instrs ->
       IdSet.add id (all_decls instrs)
    | _ :: instrs -> all_decls instrs
    | [] -> IdSet.empty
  in

  let orig_A n =
    match graph.nodes.(n) with
    | Some ((_, CF_block instrs), _, _) ->
       let vars = List.fold_left IdSet.union IdSet.empty (List.map instr_writes instrs) in
       let vars = IdSet.diff vars (all_decls instrs) in
       all_vars := IdSet.union vars !all_vars;
       vars
    | Some _ -> IdSet.empty
    | None -> IdSet.empty
  in
  let phi_A = ref Bindings.empty in

  for n = 0 to graph.next - 1 do
    IdSet.iter (fun a ->
        let ds = match Bindings.find_opt a !defsites with Some ds -> ds | None -> IntSet.empty in
        defsites := Bindings.add a (IntSet.add n ds) !defsites
      ) (orig_A n)
  done;

  IdSet.iter (fun a ->
      let workset = ref (Bindings.find a !defsites) in
      while not (IntSet.is_empty !workset) do
        let n = IntSet.choose !workset in
        workset := IntSet.remove n !workset;
        IntSet.iter (fun y ->
            let phi_A_a = match Bindings.find_opt a !phi_A with Some set -> set | None -> IntSet.empty in
            if not (IntSet.mem y phi_A_a) then
              begin
                begin match graph.nodes.(y) with
                | Some ((phis, cfnode), preds, succs) ->
                   graph.nodes.(y) <- Some ((Phi (a, Util.list_init (IntSet.cardinal preds) (fun _ -> a)) :: phis, cfnode), preds, succs)
                | None -> assert false
                end;
                phi_A := Bindings.add a (IntSet.add y phi_A_a) !phi_A;
                if not (IdSet.mem a (orig_A y)) then
                  workset := IntSet.add y !workset
              end
          ) df.(n)
      done
    ) !all_vars

let rename_variables graph root children =
  let counts = ref Bindings.empty in
  let stacks = ref Bindings.empty in

  let get_count id =
    match Bindings.find_opt id !counts with Some n -> n | None -> 0
  in
  let top_stack id =
    match Bindings.find_opt id !stacks with Some (x :: _) -> x | (Some [] | None) -> 0
  in
  let push_stack id n =
    stacks := Bindings.add id (n :: match Bindings.find_opt id !stacks with Some s -> s | None -> []) !stacks
  in

  let rec fold_frag = function
    | F_id id ->
       let i = top_stack id in
       F_id (append_id id ("_" ^ string_of_int i))
    | F_ref id ->
       let i = top_stack id in
       F_ref (append_id id ("_" ^ string_of_int i))
    | F_lit vl -> F_lit vl
    | F_have_exception -> F_have_exception
    | F_current_exception -> F_current_exception
    | F_op (f1, op, f2) -> F_op (fold_frag f1, op, fold_frag f2)
    | F_unary (op, f) -> F_unary (op, fold_frag f)
    | F_call (id, fs) -> F_call (id, List.map fold_frag fs)
    | F_field (f, field) -> F_field (fold_frag f, field)
    | F_raw str -> F_raw str
    | F_poly f -> F_poly (fold_frag f)
  in

  let rec fold_clexp = function
    | CL_id (id, ctyp) ->
       let i = get_count id + 1 in
       counts := Bindings.add id i !counts;
       push_stack id i;
       CL_id (append_id id ("_" ^ string_of_int i), ctyp)
    | CL_field (clexp, field) -> CL_field (fold_clexp clexp, field)
    | CL_addr clexp -> CL_addr (fold_clexp clexp)
    | CL_tuple (clexp, n) -> CL_tuple (fold_clexp clexp, n)
    | CL_current_exception ctyp -> CL_current_exception ctyp
    | CL_have_exception -> CL_have_exception
    | CL_return ctyp -> CL_return ctyp
    | CL_void -> CL_void
  in

  let fold_cval (f, ctyp) = (fold_frag f, ctyp) in

  let ssa_instr (I_aux (aux, annot)) =
    let aux = match aux with
      | I_funcall (clexp, extern, id, args) ->
         let args = List.map fold_cval args in
         I_funcall (fold_clexp clexp, extern, id, args)
      | I_copy (clexp, cval) ->
         let cval = fold_cval cval in
         I_copy (fold_clexp clexp, cval)
      | I_decl (ctyp, id) ->
         let i = get_count id + 1 in
         counts := Bindings.add id i !counts;
         push_stack id i;
         I_decl (ctyp, append_id id ("_" ^ string_of_int i))
      | I_init (ctyp, id, cval) ->
         let cval = fold_cval cval in
         let i = get_count id + 1 in
         counts := Bindings.add id i !counts;
         push_stack id i;
         I_init (ctyp, append_id id ("_" ^ string_of_int i), cval)
      | instr -> instr
    in
    I_aux (aux, annot)
  in

  let ssa_cfnode = function
    | CF_start -> CF_start
    | CF_block instrs -> CF_block (List.map ssa_instr instrs)
    | CF_label label -> CF_label label
  in

  let ssa_ssanode = function
    | Phi (id, args) ->
       let i = get_count id + 1 in
       counts := Bindings.add id i !counts;
       push_stack id i;
       Phi (append_id id ("_" ^ string_of_int i), args)
  in

  let fix_phi j = function
    | Phi (id, ids) ->
       Phi (id, List.mapi (fun k a ->
                    if k = j then
                      let i = top_stack a in
                      append_id a ("_" ^ string_of_int i)
                    else a)
                  ids)
  in

  let rec rename n =
    let old_stacks = !stacks in
    begin match graph.nodes.(n) with
    | Some ((ssa, cfnode), preds, succs) ->
       let ssa = List.map ssa_ssanode ssa in
       graph.nodes.(n) <- Some ((ssa, ssa_cfnode cfnode), preds, succs);
       List.iter (fun succ ->
           match graph.nodes.(succ) with
           | Some ((ssa, cfnode), preds, succs) ->
              (* Suppose n is the j-th predecessor of succ *)
              let rec find_j n succ = function
                | pred :: preds ->
                   if pred = succ then n else find_j (n + 1) succ preds
                | [] -> assert false
              in
              let j = find_j 0 n (IntSet.elements preds) in
              graph.nodes.(succ) <- Some ((List.map (fix_phi j) ssa, cfnode), preds, succs)
           | None -> assert false
         ) (IntSet.elements succs)
    | None -> assert false
    end;
    IntSet.iter (fun child -> rename child) (children.(n));
    stacks := old_stacks
  in
  rename root

let ssa instrs =
  let start, finish, cfg = control_flow_graph instrs in
  let idom = immediate_dominators cfg start in
  let children = dominator_children idom in
  let df = dominance_frontiers cfg start idom children in
  place_phi_functions cfg df;
  rename_variables cfg start children;
  cfg

(* Debugging utilities for outputing Graphviz files. *)

let string_of_phis = function
  | [] -> ""
  | phis -> Util.string_of_list "\\l" (fun (Phi (id, args)) -> string_of_id id ^ " = phi(" ^ Util.string_of_list ", " string_of_id args ^ ")") phis ^ "\\l"

let string_of_node = function
  | (phis, CF_label label) -> string_of_phis phis ^ label
  | (phis, CF_block instrs) -> string_of_phis phis ^ Util.string_of_list "\\l" (fun instr -> String.escaped (Pretty_print_sail.to_string (pp_instr ~short:true instr))) instrs
  | (phis, CF_start) -> string_of_phis phis ^ "START"

let vertex_color = function
  | (_, CF_start)   -> "peachpuff"
  | (_, CF_block _) -> "white"
  | (_, CF_label _) -> "springgreen"

let edge_color node_from node_to =
  match node_from, node_to with
  | CF_block _, CF_block _ -> "black"
  | CF_label _, CF_block _ -> "red"
  | CF_block _, CF_label _ -> "blue"
  | _, _ -> "deeppink"

let make_dot out_chan graph =
  Util.opt_colors := false;
  output_string out_chan "digraph DEPS {\n";
  let make_node i n =
    output_string out_chan (Printf.sprintf "  n%i [label=\"%s\";shape=box;style=filled;fillcolor=%s];\n" i (string_of_node n) (vertex_color n))
  in
  let make_line i s =
    output_string out_chan (Printf.sprintf "  n%i -> n%i [color=black];\n" i s)
  in
  for i = 0 to graph.next - 1 do
    match graph.nodes.(i) with
    | Some (n, _, successors) ->
       make_node i n;
       IntSet.iter (fun s -> make_line i s) successors
    | None -> ()
  done;
  output_string out_chan "}\n";
  Util.opt_colors := true

let make_dominators_dot out_chan idom graph =
  Util.opt_colors := false;
  output_string out_chan "digraph DOMS {\n";
  let make_node i n =
    output_string out_chan (Printf.sprintf "  n%i [label=\"%s\";shape=box;style=filled;fillcolor=%s];\n" i (string_of_node n) (vertex_color n))
  in
  let make_line i s =
    output_string out_chan (Printf.sprintf "  n%i -> n%i [color=black];\n" i s)
  in
  for i = 0 to Array.length idom - 1 do
    match graph.nodes.(i) with
    | Some (n, _, _) ->
       if idom.(i) = -1 then
         make_node i n
       else
         (make_node i n; make_line i idom.(i))
    | None -> ()
  done;
  output_string out_chan "}\n";
  Util.opt_colors := true
