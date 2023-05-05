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

open Ast_util
open Jib
open Jib_util

module IntSet = Set.Make (struct
  type t = int
  let compare = compare
end)
module IntMap = Map.Make (struct
  type t = int
  let compare = compare
end)

(**************************************************************************)
(* 1. Mutable graph type                                                  *)
(**************************************************************************)

type 'a array_graph = {
  mutable next : int;
  mutable nodes : ('a * IntSet.t * IntSet.t) option array;
  mutable next_cond : int;
  mutable conds : cval IntMap.t;
}

let make ~initial_size () = { next = 0; nodes = Array.make initial_size None; next_cond = 1; conds = IntMap.empty }

let get_cond graph n = if n >= 0 then IntMap.find n graph.conds else V_call (Bnot, [IntMap.find (abs n) graph.conds])

let get_vertex graph n = graph.nodes.(n)

let iter_graph f graph =
  for n = 0 to graph.next - 1 do
    match graph.nodes.(n) with Some (x, y, z) -> f x y z | None -> ()
  done

let add_cond cval graph =
  let n = graph.next_cond in
  graph.conds <- IntMap.add n cval graph.conds;
  graph.next_cond <- n + 1;
  n

(** Add a vertex to a graph, returning the node index *)
let add_vertex data graph =
  let n = graph.next in
  if n >= Array.length graph.nodes then begin
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
  begin
    match graph.nodes.(n) with
    | Some (data, parents, children) -> graph.nodes.(n) <- Some (data, parents, IntSet.add m children)
    | None -> raise (Invalid_argument "Parent node does not exist in graph")
  end;
  match graph.nodes.(m) with
  | Some (data, parents, children) -> graph.nodes.(m) <- Some (data, IntSet.add n parents, children)
  | None -> raise (Invalid_argument "Child node does not exist in graph")

let cardinal graph = graph.next

let reachable roots graph =
  let visited = ref IntSet.empty in

  let rec reachable' n =
    if IntSet.mem n !visited then ()
    else begin
      visited := IntSet.add n !visited;
      match graph.nodes.(n) with Some (_, _, successors) -> IntSet.iter reachable' successors | None -> ()
    end
  in
  IntSet.iter reachable' roots;
  !visited

exception Not_a_DAG of int

let topsort graph =
  let marked = ref IntSet.empty in
  let temp_marked = ref IntSet.empty in
  let list = ref [] in

  let rec visit node =
    if IntSet.mem node !temp_marked then raise (Not_a_DAG node)
    else if IntSet.mem node !marked then ()
    else begin
      match get_vertex graph node with
      | None -> failwith "Node does not exist in topsort"
      | Some (_, _, succs) ->
          temp_marked := IntSet.add node !temp_marked;
          IntSet.iter visit succs;
          marked := IntSet.add node !marked;
          temp_marked := IntSet.remove node !temp_marked;
          list := node :: !list
    end
  in

  let find_unmarked () =
    let unmarked = ref (-1) in
    let i = ref 0 in
    while !unmarked = -1 && !i < Array.length graph.nodes do
      begin
        match get_vertex graph !i with None -> () | Some _ -> if not (IntSet.mem !i !marked) then unmarked := !i
      end;
      incr i
    done;
    !unmarked
  in

  let rec topsort' () =
    let unmarked = find_unmarked () in
    if unmarked = -1 then ()
    else (
      visit unmarked;
      topsort' ()
    )
  in
  topsort' ();
  !list

let prune visited graph =
  for i = 0 to graph.next - 1 do
    match graph.nodes.(i) with
    | Some (n, preds, succs) ->
        if IntSet.mem i visited then graph.nodes.(i) <- Some (n, IntSet.inter visited preds, IntSet.inter visited succs)
        else graph.nodes.(i) <- None
    | None -> ()
  done

(**************************************************************************)
(* 2. Mutable control flow graph                                          *)
(**************************************************************************)

type terminator =
  | T_undefined of ctyp
  | T_exit of string
  | T_end of name
  | T_goto of string
  | T_jump of int * string
  | T_label of string
  | T_none

type cf_node = CF_label of string | CF_block of instr list * terminator | CF_guard of int | CF_start of ctyp NameMap.t

let to_terminator graph = function
  | I_label label -> T_label label
  | I_goto label -> T_goto label
  | I_jump (cval, label) ->
      let n = add_cond cval graph in
      T_jump (n, label)
  | I_end name -> T_end name
  | I_exit cause -> T_exit cause
  | I_undefined ctyp -> T_undefined ctyp
  | _ -> assert false

(* For now we only generate CFGs for flat lists of instructions *)
let control_flow_graph instrs =
  let module StringMap = Map.Make (String) in
  let labels = ref StringMap.empty in

  let graph = make ~initial_size:512 () in

  iter_instr
    (fun (I_aux (instr, annot)) ->
      match instr with
      | I_label label -> labels := StringMap.add label (add_vertex ([], CF_label label) graph) !labels
      | _ -> ()
    )
    (iblock instrs);

  let cf_split (I_aux (aux, _)) =
    match aux with I_label _ | I_goto _ | I_jump _ | I_end _ | I_exit _ | I_undefined _ -> true | _ -> false
  in

  let rec cfg preds instrs =
    let before, after = instr_split_at cf_split instrs in
    let terminator, after =
      match after with I_aux (instr, _) :: after -> (to_terminator graph instr, after) | [] -> (T_none, [])
    in
    let preds =
      match (before, terminator) with
      | [], (T_none | T_label _) -> preds
      | instrs, _ ->
          let n = add_vertex ([], CF_block (instrs, terminator)) graph in
          List.iter (fun p -> add_edge p n graph) preds;
          [n]
    in
    match terminator with
    | T_end _ | T_exit _ | T_undefined _ -> cfg [] after
    | T_goto label ->
        List.iter (fun p -> add_edge p (StringMap.find label !labels) graph) preds;
        cfg [] after
    | T_jump (cond, label) ->
        let t = add_vertex ([], CF_guard cond) graph in
        let f = add_vertex ([], CF_guard (-cond)) graph in
        List.iter
          (fun p ->
            add_edge p t graph;
            add_edge p f graph
          )
          preds;
        add_edge t (StringMap.find label !labels) graph;
        cfg [f] after
    | T_label label -> cfg (StringMap.find label !labels :: preds) after
    | T_none -> preds
  in

  let start = add_vertex ([], CF_start NameMap.empty) graph in
  let finish = cfg [start] instrs in

  let visited = reachable (IntSet.singleton start) graph in
  prune visited graph;

  (start, finish, graph)

(**************************************************************************)
(* 3. Computing dominators                                                *)
(**************************************************************************)

(** Calculate the (immediate) dominators of a graph using the
   Lengauer-Tarjan algorithm. This is the slightly less sophisticated
   version from Appel's book 'Modern compiler implementation in ML'
   which runs in O(n log(n)) time. *)
let immediate_dominators graph root =
  let none = -1 in
  let vertex = Array.make (cardinal graph) 0 in
  let parent = Array.make (cardinal graph) none in
  let ancestor = Array.make (cardinal graph) none in
  let semi = Array.make (cardinal graph) none in
  let idom = Array.make (cardinal graph) none in
  let samedom = Array.make (cardinal graph) none in
  let best = Array.make (cardinal graph) none in
  let dfnum = Array.make (cardinal graph) (-1) in
  let bucket = Array.make (cardinal graph) IntSet.empty in

  let rec ancestor_with_lowest_semi v =
    let a = ancestor.(v) in
    if ancestor.(a) <> none then (
      let b = ancestor_with_lowest_semi a in
      ancestor.(v) <- ancestor.(a);
      if dfnum.(semi.(b)) < dfnum.(semi.(best.(v))) then best.(v) <- b else ()
    )
    else ();
    if best.(v) <> none then best.(v) else v
  in

  let link p n =
    ancestor.(n) <- p;
    best.(n) <- n
  in

  let count = ref 0 in

  let rec dfs p n =
    if dfnum.(n) = -1 then begin
      dfnum.(n) <- !count;
      vertex.(!count) <- n;
      parent.(n) <- p;
      incr count;
      match graph.nodes.(n) with
      | Some (_, _, successors) -> IntSet.iter (fun w -> dfs n w) successors
      | None -> assert false
    end
  in
  dfs none root;

  for i = !count - 1 downto 1 do
    let n = vertex.(i) in
    let p = parent.(n) in
    let s = ref p in

    begin
      match graph.nodes.(n) with
      | Some (_, predecessors, _) ->
          IntSet.iter
            (fun v ->
              let s' = if dfnum.(v) <= dfnum.(n) then v else semi.(ancestor_with_lowest_semi v) in
              if dfnum.(s') < dfnum.(!s) then s := s'
            )
            predecessors
      | None -> assert false
    end;
    semi.(n) <- !s;
    bucket.(!s) <- IntSet.add n bucket.(!s);
    link p n;
    IntSet.iter
      (fun v ->
        let y = ancestor_with_lowest_semi v in
        if semi.(y) = semi.(v) then idom.(v) <- p else samedom.(v) <- y
      )
      bucket.(p)
  done;
  for i = 1 to !count - 1 do
    let n = vertex.(i) in
    if samedom.(n) <> none then idom.(n) <- idom.(samedom.(n))
  done;
  idom

(** [(dominator_children idoms).(n)] are the nodes whose immediate dominator
   (idom) is n. *)
let dominator_children idom =
  let none = -1 in
  let children = Array.make (Array.length idom) IntSet.empty in

  for n = 0 to Array.length idom - 1 do
    let p = idom.(n) in
    if p <> none then children.(p) <- IntSet.add n children.(p)
  done;
  children

(** [dominate idom n w] is true if n dominates w in the tree of
   immediate dominators idom. *)
let rec dominate idom n w =
  let none = -1 in
  let p = idom.(n) in
  if p = none then false else if p = w then true else dominate idom p w

let dominance_frontiers graph root idom children =
  let df = Array.make (cardinal graph) IntSet.empty in

  let rec compute_df n =
    let set = ref IntSet.empty in

    begin
      match graph.nodes.(n) with
      | Some (content, _, succs) -> IntSet.iter (fun y -> if idom.(y) <> n then set := IntSet.add y !set) succs
      | None -> ()
    end;
    IntSet.iter
      (fun c ->
        compute_df c;
        IntSet.iter (fun w -> if not (dominate idom n w) then set := IntSet.add w !set) df.(c)
      )
      children.(n);
    df.(n) <- !set
  in
  compute_df root;
  df

(**************************************************************************)
(* 4. Conversion to SSA form                                              *)
(**************************************************************************)

type ssa_elem = Phi of Jib.name * Jib.ctyp * Jib.name list | Pi of Jib.cval list

let place_phi_functions graph df =
  let defsites = ref NameCTMap.empty in

  let all_vars = ref NameCTSet.empty in

  let rec all_decls = function
    | I_aux ((I_init (ctyp, id, _) | I_decl (ctyp, id)), _) :: instrs -> NameCTSet.add (id, ctyp) (all_decls instrs)
    | _ :: instrs -> all_decls instrs
    | [] -> NameCTSet.empty
  in

  let orig_A n =
    match graph.nodes.(n) with
    | Some ((_, CF_block (instrs, _)), _, _) ->
        let vars = List.fold_left NameCTSet.union NameCTSet.empty (List.map instr_typed_writes instrs) in
        let vars = NameCTSet.diff vars (all_decls instrs) in
        all_vars := NameCTSet.union vars !all_vars;
        vars
    | Some _ -> NameCTSet.empty
    | None -> NameCTSet.empty
  in
  let phi_A = ref NameCTMap.empty in

  for n = 0 to graph.next - 1 do
    NameCTSet.iter
      (fun a ->
        let ds = match NameCTMap.find_opt a !defsites with Some ds -> ds | None -> IntSet.empty in
        defsites := NameCTMap.add a (IntSet.add n ds) !defsites
      )
      (orig_A n)
  done;

  NameCTSet.iter
    (fun a ->
      let workset = ref (NameCTMap.find a !defsites) in
      while not (IntSet.is_empty !workset) do
        let n = IntSet.choose !workset in
        workset := IntSet.remove n !workset;
        IntSet.iter
          (fun y ->
            let phi_A_a = match NameCTMap.find_opt a !phi_A with Some set -> set | None -> IntSet.empty in
            if not (IntSet.mem y phi_A_a) then begin
              begin
                match graph.nodes.(y) with
                | Some ((phis, cfnode), preds, succs) ->
                    graph.nodes.(y) <-
                      Some
                        ( (Phi (fst a, snd a, Util.list_init (IntSet.cardinal preds) (fun _ -> fst a)) :: phis, cfnode),
                          preds,
                          succs
                        )
                | None -> assert false
              end;
              phi_A := NameCTMap.add a (IntSet.add y phi_A_a) !phi_A;
              if not (NameCTSet.mem a (orig_A y)) then workset := IntSet.add y !workset
            end
          )
          df.(n)
      done
    )
    !all_vars

let rename_variables graph root children =
  let counts = ref NameMap.empty in
  let stacks = ref NameMap.empty in

  let phi_zeros = ref NameMap.empty in

  let ssa_name i = function
    | Name (id, _) -> Name (id, i)
    | Global (id, _) -> Global (id, i)
    | Have_exception _ -> Have_exception i
    | Current_exception _ -> Current_exception i
    | Throw_location _ -> Throw_location i
    | Return _ -> Return i
  in

  let get_count id = match NameMap.find_opt id !counts with Some n -> n | None -> 0 in
  let top_stack id = match NameMap.find_opt id !stacks with Some (x :: _) -> x | Some [] -> 0 | None -> 0 in
  let top_stack_phi id ctyp =
    match NameMap.find_opt id !stacks with
    | Some (x :: _) -> x
    | Some [] -> 0
    | None ->
        phi_zeros := NameMap.add (ssa_name 0 id) ctyp !phi_zeros;
        0
  in
  let push_stack id n =
    stacks := NameMap.add id (n :: (match NameMap.find_opt id !stacks with Some s -> s | None -> [])) !stacks
  in

  let rec fold_cval = function
    | V_id (id, ctyp) ->
        let i = top_stack id in
        V_id (ssa_name i id, ctyp)
    | V_lit (vl, ctyp) -> V_lit (vl, ctyp)
    | V_call (id, fs) -> V_call (id, List.map fold_cval fs)
    | V_field (f, field) -> V_field (fold_cval f, field)
    | V_tuple_member (f, len, n) -> V_tuple_member (fold_cval f, len, n)
    | V_ctor_kind (f, ctor, ctyp) -> V_ctor_kind (fold_cval f, ctor, ctyp)
    | V_ctor_unwrap (f, ctor, ctyp) -> V_ctor_unwrap (fold_cval f, ctor, ctyp)
    | V_struct (fields, ctyp) -> V_struct (List.map (fun (field, cval) -> (field, fold_cval cval)) fields, ctyp)
    | V_tuple (members, ctyp) -> V_tuple (List.map fold_cval members, ctyp)
  in

  let rec fold_clexp rmw = function
    | CL_id (id, ctyp) when rmw ->
        let i = top_stack id in
        let j = get_count id + 1 in
        counts := NameMap.add id j !counts;
        push_stack id j;
        CL_rmw (ssa_name i id, ssa_name j id, ctyp)
    | CL_id (id, ctyp) ->
        let i = get_count id + 1 in
        counts := NameMap.add id i !counts;
        push_stack id i;
        CL_id (ssa_name i id, ctyp)
    | CL_rmw _ -> assert false
    | CL_field (clexp, field) -> CL_field (fold_clexp true clexp, field)
    | CL_addr clexp -> CL_addr (fold_clexp false clexp)
    | CL_tuple (clexp, n) -> CL_tuple (fold_clexp true clexp, n)
    | CL_void -> CL_void
  in

  let ssa_instr (I_aux (aux, annot)) =
    let aux =
      match aux with
      | I_funcall (clexp, extern, id, args) ->
          let args = List.map fold_cval args in
          I_funcall (fold_clexp false clexp, extern, id, args)
      | I_copy (clexp, cval) ->
          let cval = fold_cval cval in
          I_copy (fold_clexp false clexp, cval)
      | I_decl (ctyp, id) ->
          let i = get_count id + 1 in
          counts := NameMap.add id i !counts;
          push_stack id i;
          I_decl (ctyp, ssa_name i id)
      | I_init (ctyp, id, cval) ->
          let cval = fold_cval cval in
          let i = get_count id + 1 in
          counts := NameMap.add id i !counts;
          push_stack id i;
          I_init (ctyp, ssa_name i id, cval)
      | instr -> instr
    in
    I_aux (aux, annot)
  in

  let ssa_terminator = function
    | T_jump (cond, label) -> begin
        match IntMap.find_opt cond graph.conds with
        | Some cval ->
            graph.conds <- IntMap.add cond (fold_cval cval) graph.conds;
            T_jump (cond, label)
        | None -> assert false
      end
    | T_end id ->
        let i = top_stack id in
        T_end (ssa_name i id)
    | terminator -> terminator
  in

  let ssa_cfnode = function
    | CF_start inits -> CF_start inits
    | CF_block (instrs, terminator) ->
        let instrs = List.map ssa_instr instrs in
        CF_block (instrs, ssa_terminator terminator)
    | CF_label label -> CF_label label
    | CF_guard cond -> CF_guard cond
  in

  let ssa_ssanode = function
    | Phi (id, ctyp, args) ->
        let i = get_count id + 1 in
        counts := NameMap.add id i !counts;
        push_stack id i;
        Phi (ssa_name i id, ctyp, args)
    | Pi _ -> assert false (* Should not be introduced at this point *)
  in

  let fix_phi j = function
    | Phi (id, ctyp, ids) ->
        let fix_arg k a =
          if k = j then (
            let i = top_stack_phi a ctyp in
            ssa_name i a
          )
          else a
        in
        Phi (id, ctyp, List.mapi fix_arg ids)
    | Pi _ -> assert false (* Should not be introduced at this point *)
  in

  let rec rename n =
    let old_stacks = !stacks in
    begin
      match graph.nodes.(n) with
      | Some ((ssa, cfnode), preds, succs) ->
          let ssa = List.map ssa_ssanode ssa in
          graph.nodes.(n) <- Some ((ssa, ssa_cfnode cfnode), preds, succs);
          List.iter
            (fun succ ->
              match graph.nodes.(succ) with
              | Some ((ssa, cfnode), preds, succs) ->
                  (* Suppose n is the j-th predecessor of succ *)
                  let rec find_j n succ = function
                    | pred :: preds -> if pred = succ then n else find_j (n + 1) succ preds
                    | [] -> assert false
                  in
                  let j = find_j 0 n (IntSet.elements preds) in
                  graph.nodes.(succ) <- Some ((List.map (fix_phi j) ssa, cfnode), preds, succs)
              | None -> assert false
            )
            (IntSet.elements succs)
      | None -> assert false
    end;
    IntSet.iter (fun child -> rename child) children.(n);
    stacks := old_stacks
  in
  rename root;
  match graph.nodes.(root) with
  | Some ((ssa, CF_start _), preds, succs) -> graph.nodes.(root) <- Some ((ssa, CF_start !phi_zeros), preds, succs)
  | _ -> failwith "root node is not CF_start"

let place_pi_functions graph start idom children =
  let get_guard = function
    | CF_guard cond -> begin
        match IntMap.find_opt (abs cond) graph.conds with
        | Some guard when cond > 0 -> [guard]
        | Some guard -> [V_call (Bnot, [guard])]
        | None -> assert false
      end
    | _ -> []
  in
  let get_pi_contents ssanodes = List.concat (List.map (function Pi guards -> guards | _ -> []) ssanodes) in

  let rec go n =
    begin
      match graph.nodes.(n) with
      | Some ((ssa, cfnode), preds, succs) ->
          let p = idom.(n) in
          if p <> -1 then begin
            match graph.nodes.(p) with
            | Some ((dom_ssa, _), _, _) ->
                let args = get_guard cfnode @ get_pi_contents dom_ssa in
                graph.nodes.(n) <- Some ((Pi args :: ssa, cfnode), preds, succs)
            | None -> assert false
          end
      | None -> assert false
    end;
    IntSet.iter go children.(n)
  in
  go start

(** Remove p nodes. Assumes the graph is acyclic. *)
let remove_nodes remove_cf graph =
  for n = 0 to graph.next - 1 do
    match graph.nodes.(n) with
    | Some ((_, cfnode), preds, succs) when remove_cf cfnode ->
        IntSet.iter
          (fun pred ->
            match graph.nodes.(pred) with
            | Some (content, preds', succs') ->
                graph.nodes.(pred) <- Some (content, preds', IntSet.remove n (IntSet.union succs succs'))
            | None -> assert false
          )
          preds;
        IntSet.iter
          (fun succ ->
            match graph.nodes.(succ) with
            | Some (content, preds', succs') ->
                graph.nodes.(succ) <- Some (content, IntSet.remove n (IntSet.union preds preds'), succs')
            | None -> assert false
          )
          succs;
        graph.nodes.(n) <- None
    | _ -> ()
  done

let ssa instrs =
  let start, finish, cfg = control_flow_graph instrs in
  let idom = immediate_dominators cfg start in
  let children = dominator_children idom in
  let df = dominance_frontiers cfg start idom children in
  place_phi_functions cfg df;
  rename_variables cfg start children;
  place_pi_functions cfg start idom children;
  (start, cfg)

(* Debugging utilities for outputing Graphviz files. *)

let string_of_ssainstr = function
  | Phi (id, ctyp, args) ->
      string_of_name id ^ " : " ^ string_of_ctyp ctyp ^ " = &phi;(" ^ Util.string_of_list ", " string_of_name args ^ ")"
  | Pi cvals -> "&pi;(" ^ Util.string_of_list ", " (fun v -> String.escaped (string_of_cval v)) cvals ^ ")"

let string_of_phis = function [] -> "" | phis -> Util.string_of_list "\\l" string_of_ssainstr phis ^ "\\l"

let string_of_node = function
  | phis, CF_label label -> string_of_phis phis ^ label
  | phis, CF_block (instrs, terminator) ->
      let string_of_instr instr =
        let buf = Buffer.create 128 in
        Jib_ir.Flat_ir_formatter.output_instr 0 buf 0 Jib_ir.StringMap.empty instr;
        Buffer.contents buf
      in
      string_of_phis phis ^ Util.string_of_list "\\l" (fun instr -> String.escaped (string_of_instr instr)) instrs
  | phis, CF_start inits -> string_of_phis phis ^ "START"
  | phis, CF_guard cval -> string_of_phis phis ^ string_of_int cval

let vertex_color = function
  | _, CF_start _ -> "peachpuff"
  | _, CF_block _ -> "white"
  | _, CF_label _ -> "springgreen"
  | _, CF_guard _ -> "yellow"

let make_dot out_chan graph =
  Util.opt_colors := false;
  output_string out_chan "digraph DEPS {\n";
  let make_node i n =
    output_string out_chan
      (Printf.sprintf "  n%i [label=\"%i\\n%s\\l\";shape=box;style=filled;fillcolor=%s];\n" i i (string_of_node n)
         (vertex_color n)
      )
  in
  let make_line i s = output_string out_chan (Printf.sprintf "  n%i -> n%i [color=black];\n" i s) in
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
    output_string out_chan
      (Printf.sprintf "  n%i [label=\"%i\\n%s\\l\";shape=box;style=filled;fillcolor=%s];\n" i i (string_of_node n)
         (vertex_color n)
      )
  in
  let make_line i s = output_string out_chan (Printf.sprintf "  n%i -> n%i [color=black];\n" i s) in
  for i = 0 to Array.length idom - 1 do
    match graph.nodes.(i) with
    | Some (n, _, _) ->
        if idom.(i) = -1 then make_node i n
        else (
          make_node i n;
          make_line i idom.(i)
        )
    | None -> ()
  done;
  output_string out_chan "}\n";
  Util.opt_colors := true
