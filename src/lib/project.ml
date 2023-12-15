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

include Visitor

module StringSet = Set.Make (String)
module StringMap = Util.StringMap
module ModSet = Util.IntSet
module ModMap = Util.IntMap
module ModGraph = Graph.Make (Int)

module ModId = struct
  type t = int

  let to_int mod_id = mod_id
end

type mod_id = ModId.t

let global_scope = -1

type l = Lexing.position * Lexing.position

let to_loc l = Parse_ast.Range (fst l, snd l)

type 'a spanned = 'a * l

(**************************************************************************)
(* Module file AST and visitor class, and evaluation visitor              *)
(**************************************************************************)

type selector = S_tree | S_only

type value = V_string of string | V_bool of bool | V_selector of selector * string | V_list of value list

let string_value s = V_string s
let bool_value b = V_bool b

let parse_assignment ~variables s =
  match String.index_from_opt s 0 '=' with
  | None -> false
  | Some n ->
      let var = String.trim (String.sub s 0 n) in
      let arg =
        match String.trim (String.sub s (n + 1) (String.length s - (n + 1))) with
        | "true" -> V_bool true
        | "false" -> V_bool false
        | s -> V_string s
      in
      variables := StringMap.add var arg !variables;
      true

type exp =
  | E_app of string * exp spanned list
  | E_file of string
  | E_id of string
  | E_if of exp spanned * exp spanned * exp spanned
  | E_list of exp spanned list
  | E_op of exp spanned * string * exp spanned
  | E_parent
  | E_string of string
  | E_value of value
  | E_var of string

type 'a non_empty = 'a * 'a list

type dependency =
  | D_requires of exp spanned non_empty
  | D_after of exp spanned non_empty
  | D_before of exp spanned non_empty
  | D_default
  | D_optional

type mdl_def = M_dep of dependency | M_directory of exp spanned | M_module of mdl | M_files of exp spanned non_empty

and mdl = { name : string spanned; defs : mdl_def spanned list; span : l }

type def = Def_root of string | Def_var of string spanned * exp spanned | Def_module of mdl | Def_test of string list

let mk_root root = (Def_root root, (Lexing.dummy_pos, Lexing.dummy_pos))

class type project_visitor = object
  method vexp : exp spanned -> exp spanned visit_action
  method vdependency : l -> dependency -> dependency visit_action
  method vmodule : mdl -> mdl visit_action
  method vdef : def spanned -> def spanned visit_action

  method on_root_change : string -> unit

  method short_circuit_if : bool
end

let rec visit_exp vis outer_exp =
  let aux vis no_change =
    match no_change with
    | E_file _, _ | E_string _, _ | E_id _, _ | E_var _, _ | E_parent, _ | E_value _, _ -> no_change
    | E_if (i, t, e), l ->
        let i' = visit_exp vis i in
        begin
          match i' with
          | E_value (V_bool b), _ when vis#short_circuit_if -> if b then visit_exp vis t else visit_exp vis e
          | _ ->
              let t' = visit_exp vis t in
              let e' = visit_exp vis e in
              if i == i' && t == t' && e == e' then no_change else (E_if (i', t', e'), l)
        end
    | E_list xs, l ->
        let xs' = map_no_copy (visit_exp vis) xs in
        if xs == xs' then no_change else (E_list xs', l)
    | E_op (lhs, op, rhs), l ->
        let lhs' = visit_exp vis lhs in
        let rhs' = visit_exp vis rhs in
        if lhs == lhs' && rhs == rhs' then no_change else (E_op (lhs', op, rhs'), l)
    | E_app (f, xs), l ->
        let xs' = map_no_copy (visit_exp vis) xs in
        if xs == xs' then no_change else (E_app (f, xs'), l)
  in
  do_visit vis (vis#vexp outer_exp) aux outer_exp

let visit_dependency vis l outer_dependency =
  let aux vis no_change =
    match no_change with
    | D_requires (e, es) ->
        let e' = visit_exp vis e in
        let es' = map_no_copy (visit_exp vis) es in
        if e == e' && es == es' then no_change else D_requires (e', es')
    | D_after (e, es) ->
        let e' = visit_exp vis e in
        let es' = map_no_copy (visit_exp vis) es in
        if e == e' && es == es' then no_change else D_after (e', es')
    | D_before (e, es) ->
        let e' = visit_exp vis e in
        let es' = map_no_copy (visit_exp vis) es in
        if e == e' && es == es' then no_change else D_before (e', es')
    | D_default | D_optional -> no_change
  in
  do_visit vis (vis#vdependency l outer_dependency) aux outer_dependency

let rec visit_module vis (outer_module : mdl) =
  let visit_module_def vis no_change =
    match no_change with
    | M_dep dep, l ->
        let dep' = visit_dependency vis l dep in
        if dep == dep' then no_change else (M_dep dep', l)
    | M_directory e, l ->
        let e' = visit_exp vis e in
        if e == e' then no_change else (M_directory e', l)
    | M_module m, l ->
        let m' = visit_module vis m in
        if m == m' then no_change else (M_module m', l)
    | M_files (e, es), l ->
        let e' = visit_exp vis e in
        let es' = map_no_copy (visit_exp vis) es in
        if e == e' && es == es' then no_change else (M_files (e', es'), l)
  in
  let aux vis (({ name; defs; span } : mdl) as no_change) =
    let defs' = map_no_copy (visit_module_def vis) defs in
    if defs == defs' then no_change else { name; defs = defs'; span }
  in
  do_visit vis (vis#vmodule outer_module) aux outer_module

let visit_def vis outer_def =
  let aux vis no_change =
    match no_change with
    | Def_test _, _ -> no_change
    | Def_var (v, exp), l ->
        let exp' = visit_exp vis exp in
        if exp == exp' then no_change else (Def_var (v, exp'), l)
    | Def_module m, l ->
        let m' = visit_module vis m in
        if m == m' then no_change else (Def_module m', l)
    | Def_root root, _ ->
        vis#on_root_change root;
        no_change
  in
  do_visit vis (vis#vdef outer_def) aux outer_def

let visit_defs vis defs = map_no_copy (visit_def vis) defs

let rec value_to_strings l = function
  | V_string s -> [(s, l)]
  | V_list vs -> List.concat (List.map (value_to_strings l) vs)
  | _ -> raise (Reporting.err_typ (to_loc l) "Expected strings")

let rec to_strings = function
  | (E_value v, l) :: xs -> value_to_strings l v @ to_strings xs
  | (_, l) :: _ -> raise (Reporting.err_typ (to_loc l) "String has not been evaluated")
  | [] -> []

let rec value_to_selectors l = function
  | V_selector (sel, s) -> [((sel, s), l)]
  | V_string s -> [((S_tree, s), l)]
  | V_list vs -> List.concat (List.map (value_to_selectors l) vs)
  | _ -> raise (Reporting.err_typ (to_loc l) "Expected module selector")

let rec to_selectors = function
  | (E_value v, l) :: xs -> value_to_selectors l v @ to_selectors xs
  | (_, l) :: _ -> raise (Reporting.err_typ (to_loc l) "Module selector has not been evaluated")
  | [] -> []

class empty_project_visitor : project_visitor =
  object
    method vexp _ = DoChildren
    method vdependency _ _ = DoChildren
    method vmodule _ = DoChildren
    method vdef _ = DoChildren

    method on_root_change _ = ()

    method short_circuit_if = false
  end

let project_binop l op lhs rhs =
  let invalid_arguments () = raise (Reporting.err_typ (to_loc l) ("Invalid arguments for '" ^ op ^ "'")) in
  match op with
  | "==" -> (
      match (lhs, rhs) with
      | V_string s1, V_string s2 -> V_bool (s1 = s2)
      | V_bool b1, V_bool b2 -> V_bool (b1 = b2)
      | _, _ -> invalid_arguments ()
    )
  | "!=" -> (
      match (lhs, rhs) with
      | V_string s1, V_string s2 -> V_bool (s1 <> s2)
      | V_bool b1, V_bool b2 -> V_bool (b1 <> b2)
      | _, _ -> invalid_arguments ()
    )
  | "/" -> (
      match (lhs, rhs) with
      | V_string lhs, V_string rhs -> V_string (lhs ^ Filename.dir_sep ^ rhs)
      | _, _ -> invalid_arguments ()
    )
  | _ -> raise (Reporting.err_typ (to_loc l) ("Unknown binary operator '" ^ op ^ "'"))

let project_app l f xs =
  match f with
  | "only" -> (
      match xs with
      | [V_string mod_name] -> V_selector (S_only, mod_name)
      | _ -> raise (Reporting.err_typ (to_loc l) "Invalid argument for only")
    )
  | "tree" -> (
      match xs with
      | [V_string mod_name] -> V_selector (S_tree, mod_name)
      | _ -> raise (Reporting.err_typ (to_loc l) "Invalid argument for tree")
    )
  | "error" -> (
      match xs with
      | [V_string msg] -> raise (Reporting.err_general (to_loc l) ("Error: " ^ msg))
      | _ -> raise (Reporting.err_typ (to_loc l) "Invalid arguments for error")
    )
  | _ -> raise (Reporting.err_typ (to_loc l) ("Unknown function '" ^ f ^ "'"))

class eval_visitor (vars : value StringMap.t ref) =
  object
    inherit empty_project_visitor

    val mutable declared : StringSet.t = StringSet.empty

    method! vdef def =
      let aux no_change =
        match no_change with
        | Def_var ((name, l), (E_value v, _)), _ ->
            if StringSet.mem name declared then
              raise (Reporting.err_typ (to_loc l) ("Variable " ^ name ^ " has already been declared"));
            if not (StringMap.mem name !vars) then vars := StringMap.add name v !vars;
            declared <- StringSet.add name declared;
            no_change
        | Def_var (_, (_, l)), _ -> Reporting.unreachable (to_loc l) __POS__ "Value has not been evaluated"
        | _ -> no_change
      in
      ChangeDoChildrenPost (def, aux)

    method! vexp outer_exp =
      let aux no_change =
        match no_change with
        | (E_string s | E_file s | E_id s), l -> (E_value (V_string s), l)
        | E_parent, l -> (E_value (V_string Filename.parent_dir_name), l)
        | E_var var, l -> begin
            match StringMap.find_opt var !vars with
            | Some v -> (E_value v, l)
            | None -> raise (Reporting.err_typ (to_loc l) ("Could not find variable " ^ var))
          end
        | E_op ((E_value lhs, _), op, (E_value rhs, _)), l -> (E_value (project_binop l op lhs rhs), l)
        | E_app (f, xs), l ->
            let xs =
              List.map
                (function
                  | E_value v, _ -> v
                  | _, l -> Reporting.unreachable (to_loc l) __POS__ "Argument has not been fully evaluated"
                  )
                xs
            in
            (E_value (project_app l f xs), l)
        | E_list xs, l ->
            let xs =
              List.map
                (function
                  | E_value v, _ -> v
                  | _, l -> Reporting.unreachable (to_loc l) __POS__ "Value in list has not been fully evaluated"
                  )
                xs
            in
            (E_value (V_list xs), l)
        | E_value _, _ -> no_change
        | E_if ((_, l), _, _), _ -> raise (Reporting.err_typ (to_loc l) "Expected boolean value in if")
        | _, l -> Reporting.unreachable (to_loc l) __POS__ "Value has not been fully evaluated"
      in
      ChangeDoChildrenPost (outer_exp, aux)

    method! short_circuit_if = true
  end

(**************************************************************************)
(* Project structure                                                      *)
(**************************************************************************)

type project_structure = {
  names : string spanned array;
  ids : int StringMap.t;
  mutable parents : int ModMap.t;
  mutable children : ModGraph.graph;
  mutable files : string spanned list ModMap.t;
  mutable requires : ModGraph.graph;
  mutable deps : ModGraph.graph;
  mutable optional : ModSet.t;
  mutable default : ModSet.t;
}

(* Simple visitor that visits modules in order of appearance
   (top-to-bottom) in the file, and stores their names in a
   (reverse-ordered) list. *)
class order_visitor (xs : string spanned list ref) =
  object
    inherit empty_project_visitor

    method! vexp _ = SkipChildren

    method! vmodule m =
      xs := m.name :: !xs;
      DoChildren
  end

(**************************************************************************)
(* Link parent and child modules together                                 *)
(**************************************************************************)

let add_child parent child map =
  ModMap.update parent
    (function None -> Some (ModSet.singleton child) | Some children -> Some (ModSet.add child children))
    map

let get_parents id proj =
  let parents = ref ModSet.empty in
  let rec loop child =
    match ModMap.find_opt child proj.parents with
    | Some parent ->
        parents := ModSet.add parent !parents;
        loop parent
    | None -> ()
  in
  loop id;
  !parents

let link_parent id parents proj =
  match parents with
  | parent :: _ ->
      proj.children <- add_child parent id proj.children;
      proj.parents <- ModMap.add id parent proj.parents;
      proj.deps <- ModGraph.add_edge id parent proj.deps
  | [] -> ()

let rec collect_files = function
  | (M_files (f, fs), _) :: mdefs -> to_strings (f :: fs) @ collect_files mdefs
  | _ :: mdefs -> collect_files mdefs
  | [] -> []

let add_root root_opt (file, l) =
  match root_opt with Some root -> (root ^ Filename.dir_sep ^ file, l) | None -> (file, l)

class structure_visitor (proj : project_structure) =
  object
    inherit empty_project_visitor

    val mutable parents : int list = []

    val mutable last_root : string option = None

    method! vexp _ = SkipChildren
    method! vdependency _ _ = SkipChildren

    method! vmodule m =
      let name = fst m.name in
      let id = StringMap.find name proj.ids in
      let files = collect_files m.defs in
      proj.files <- ModMap.add id (List.map (add_root last_root) files) proj.files;
      link_parent id parents proj;
      parents <- id :: parents;
      ChangeDoChildrenPost
        ( m,
          fun m ->
            parents <- List.tl parents;
            m
        )

    method! on_root_change new_root = last_root <- Some new_root
  end

(**************************************************************************)
(* Calculating dependencies                                               *)
(**************************************************************************)

type frame = {
  directory : string option;
  requires : (selector * string) spanned list;
  after : (selector * string) spanned list;
  before : (selector * string) spanned list;
  optional : bool;
  default : bool;
}

let empty_frame = { directory = None; requires = []; after = []; before = []; optional = false; default = false }

type stack = frame list

let is_default stack = List.exists (fun frame -> frame.default) stack

let is_optional stack = List.exists (fun frame -> frame.optional) stack

let get_from_frame f stack proj =
  let rec go acc = function
    | frame :: frames ->
        go
          (List.fold_left
             (fun acc ((selector, name), l) ->
               match (selector, StringMap.find_opt name proj.ids) with
               | S_only, Some id -> ModSet.add id acc
               | S_tree, Some id ->
                   ModSet.union acc (ModGraph.reachable (ModSet.singleton id) ModSet.empty proj.children)
               | _, None -> raise (Reporting.err_general (to_loc l) ("Module " ^ name ^ " does not exist"))
             )
             acc (f frame)
          )
          frames
    | [] -> acc
  in
  go ModSet.empty stack

let get_requires = get_from_frame (fun frame -> frame.requires)
let get_after = get_from_frame (fun frame -> frame.after)
let get_before = get_from_frame (fun frame -> frame.before)

let update_head f = function x :: xs -> f x :: xs | [] -> []

class dependency_visitor (proj : project_structure) =
  object
    inherit empty_project_visitor

    val mutable stack : stack = []

    method! vexp _ = SkipChildren

    method! vdependency _ dep =
      begin
        match dep with
        | D_requires (e, es) ->
            stack <- update_head (fun frame -> { frame with requires = frame.requires @ to_selectors (e :: es) }) stack
        | D_before (e, es) ->
            stack <- update_head (fun frame -> { frame with before = frame.before @ to_selectors (e :: es) }) stack
        | D_after (e, es) ->
            stack <- update_head (fun frame -> { frame with after = frame.after @ to_selectors (e :: es) }) stack
        | D_default -> stack <- update_head (fun frame -> { frame with default = true }) stack
        | D_optional -> stack <- update_head (fun frame -> { frame with optional = true }) stack
      end;
      SkipChildren

    method! vmodule m =
      let name = fst m.name in
      let l = snd m.name in
      let id = StringMap.find name proj.ids in
      stack <- empty_frame :: stack;
      ChangeDoChildrenPost
        ( m,
          fun m ->
            let requires = get_requires stack proj in
            let before = get_before stack proj in
            let after = get_after stack proj in

            proj.requires <- ModMap.add id (ModSet.union (get_parents id proj) requires) proj.requires;

            proj.deps <- ModGraph.add_edges id [] proj.deps;
            proj.deps <- ModSet.fold (fun r -> ModGraph.add_edge id r) requires proj.deps;
            proj.deps <- ModSet.fold (fun b -> ModGraph.add_edge b id) before proj.deps;
            proj.deps <- ModSet.fold (fun a -> ModGraph.add_edge id a) after proj.deps;

            let optional = is_optional stack in
            let default = is_default stack in
            if optional && default then
              raise (Reporting.err_general (to_loc l) (name ^ " is marked as both optional and default"))
            else if optional then proj.optional <- ModSet.add id proj.optional
            else if default then proj.default <- ModSet.add id proj.default;

            stack <- List.tl stack;
            m
        )
  end

let run_tests defs (proj : project_structure) =
  let run_test_cmd l cmd args =
    let invalid_cmd () = raise (Reporting.err_general (to_loc l) ("Invalid test command " ^ cmd)) in
    match cmd with
    | "dep_graph" ->
        (* First argument determines where we print the graph *)
        let chan =
          match List.nth_opt args 0 with Some "stderr" -> stderr | Some "stdout" -> stdout | _ -> invalid_cmd ()
        in
        let reduce_req = match List.nth_opt args 1 with Some "reduce_req" -> true | _ -> false in
        let darken id color = match ModMap.find_opt id proj.files with Some [] -> color | _ -> color ^ "3" in
        ModGraph.make_multi_dot
          ~node_color:(fun id ->
            darken id
              ( if ModSet.mem id proj.optional then "aquamarine"
                else if ModSet.mem id proj.default then "lemonchiffon"
                else "chartreuse"
              )
          )
          ~edge_color:(fun _ _ -> "black")
          ~string_of_node:(fun id -> fst proj.names.(id))
          chan
          [
            ("dotted", ModGraph.reverse (ModGraph.transitive_reduction proj.deps));
            ( "solid",
              ModGraph.reverse (if reduce_req then ModGraph.transitive_reduction proj.requires else proj.requires)
            );
          ]
    | _ -> ()
  in
  List.iter (function Def_test (cmd :: args), l -> run_test_cmd l cmd args | _ -> ()) defs

let initialize_project_structure ~variables defs =
  (* Visit all the declared modules and assign them module ids *)
  let xs = ref [] in
  let _ = visit_defs (new order_visitor xs) defs in
  let names = Array.of_list (List.rev !xs) in
  let ids =
    snd (Array.fold_left (fun (n, m) name -> (n + 1, StringMap.add (fst name) n m)) (0, StringMap.empty) names)
  in
  (* Evaluate the expressions in the project file *)
  let defs = visit_defs (new eval_visitor variables) defs in
  let proj =
    {
      names;
      ids;
      parents = ModMap.empty;
      children = ModMap.empty;
      files = ModMap.empty;
      requires = ModMap.empty;
      deps = ModGraph.empty;
      optional = ModSet.empty;
      default = ModSet.empty;
    }
  in
  (* Fill in the mutable fields of the project *)
  let _ = visit_defs (new structure_visitor proj) defs in
  let _ = visit_defs (new dependency_visitor proj) defs in
  (* Finally evaluate any __test definitions *)
  run_tests defs proj;
  proj

let rec shorten_scc loop g =
  match loop with
  | x :: xs -> begin
      match Util.find_next (fun y -> ModGraph.has_edge x y g) (List.rev xs) with
      | tail, Some (y, _) -> x :: shorten_scc (y :: List.rev tail) g
      | tail, None -> x :: shorten_scc (List.rev tail) g
    end
  | [] -> []

let get_module_id proj name = StringMap.find_opt name proj.ids

let get_children id proj = ModGraph.reachable (ModSet.singleton id) ModSet.empty proj.children

let required_modules ~roots (proj : project_structure) =
  let reqs = ModGraph.prune roots ModSet.empty proj.requires in
  fun id -> ModMap.mem id reqs

let valid_module_id proj id = 0 <= id && id < Array.length proj.names

let module_name proj id = proj.names.(id)

let module_order proj =
  let original_order = List.init (Array.length proj.names) (fun x -> x) in
  let sccs : int list list = ModGraph.scc ~original_order proj.deps in
  let rec flatten = function
    | [id] :: components -> id :: flatten components
    | [] -> []
    | (id :: ids) :: _ ->
        let name, l = proj.names.(id) in
        let loop = shorten_scc (id :: ids) proj.deps in
        let loop = Util.string_of_list " -> " (fun id -> fst proj.names.(id)) loop ^ " -> " ^ fst proj.names.(id) in
        raise
          (Reporting.err_general (to_loc l)
             ("Cyclic modules detected: " ^ name ^ " depends on itself\n\nCycle: " ^ loop)
          )
    | [] :: _ -> Reporting.unreachable Parse_ast.Unknown __POS__ "Empty component"
  in
  flatten sccs

let module_files proj id = ModMap.find id proj.files

let module_requires (proj : project_structure) id = ModMap.find id proj.requires |> ModSet.elements

let all_files proj = List.map (fun id -> ModMap.find id proj.files) (module_order proj) |> List.concat

let all_modules proj = List.map snd (StringMap.bindings proj.ids)
