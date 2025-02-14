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
(*    Louis-Emile Ploix                                                     *)
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

open Libsail

open Ast_util
open Jib
open Jib_util
open Jib_visitor
open Smt_exp
open Sv_ir

module IntSet = Util.IntSet
module IntMap = Util.IntMap

let profile_rewrite ~message f defs =
  let p = Profile.start () in
  let defs = f defs in
  Profile.finish message p;
  defs

module RemoveUnitPorts = struct
  type port_action = Keep_port | Remove_port

  let is_unit_port (port : sv_module_port) = match port.typ with CT_unit -> true | _ -> false

  let port_var (port : sv_module_port) = mk_def (SVD_var (port.name, port.typ))

  let scan_ports ports = List.map (fun port -> if is_unit_port port then Remove_port else Keep_port) ports

  let apply_port_action action x = match action with Keep_port -> Some x | Remove_port -> None

  class unit_port_visitor port_actions : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren
      method! vstatement _ = SkipChildren

      method! vdef =
        function
        | SVD_aux (SVD_module { name; recursive; input_ports; output_ports; defs }, l) ->
            port_actions := SVNameMap.add name (scan_ports input_ports, scan_ports output_ports) !port_actions;
            let unit_inputs, input_ports = List.partition is_unit_port input_ports in
            let unit_outputs, output_ports = List.partition is_unit_port output_ports in
            SVD_aux
              ( SVD_module
                  {
                    name;
                    recursive;
                    input_ports;
                    output_ports;
                    defs = List.map port_var unit_inputs @ List.map port_var unit_outputs @ defs;
                  },
                l
              )
            |> change_do_children
        | _ -> SkipChildren
    end

  class unit_connection_visitor port_actions : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren
      method! vstatement _ = SkipChildren

      method! vdef =
        function
        | SVD_aux (SVD_instantiate { module_name; instance_name; input_connections; output_connections }, l) -> begin
            match SVNameMap.find_opt module_name port_actions with
            | Some (input_port_action, output_port_action) ->
                let input_connections =
                  List.map2 apply_port_action input_port_action input_connections |> Util.option_these
                in
                let output_connections =
                  List.map2 apply_port_action output_port_action output_connections |> Util.option_these
                in
                ChangeTo
                  (SVD_aux (SVD_instantiate { module_name; instance_name; input_connections; output_connections }, l))
            | None -> SkipChildren
          end
        | _ -> DoChildren
    end

  let rewrite defs =
    let port_actions = ref SVNameMap.empty in
    let defs = visit_sv_defs (new unit_port_visitor port_actions) defs in
    visit_sv_defs (new unit_connection_visitor !port_actions) defs
end

let remove_unit_ports = profile_rewrite RemoveUnitPorts.rewrite ~message:"Removing unit ports"

module SimpSMT = struct
  class simp_smt_visitor : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vsmt_exp exp = ChangeTo (Smt_exp.simp SimpSet.empty exp)
    end

  let rewrite defs = visit_sv_defs (new simp_smt_visitor) defs
end

let simplify_smt = profile_rewrite SimpSMT.rewrite ~message:"Simplifying SMT"

module RemoveNulls = struct
  class remove_null_visitor : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren

      method! vstatement _ = DoChildren

      method! vdef =
        function
        | SVD_aux (SVD_module m, l) ->
            if List.exists is_null_def m.defs then
              change_do_children
                (SVD_aux (SVD_module { m with defs = List.filter (fun def -> not (is_null_def def)) m.defs }, l))
            else DoChildren
        | _ -> DoChildren
    end

  let rewrite defs = visit_sv_defs (new remove_null_visitor) defs
end

let remove_nulls = profile_rewrite RemoveNulls.rewrite ~message:"Removing null definitions"

module RemoveUnusedVariables = struct
  class number_var_visitor : svir_visitor =
    object
      inherit empty_svir_visitor

      val mutable num = 0

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren

      method! vdef =
        function
        | SVD_aux (SVD_var (name, ctyp), l) ->
            num <- num + 1;
            ChangeTo (SVD_aux (SVD_var (name, ctyp), Unique (num - 1, l)))
        | SVD_aux (SVD_module m, l) ->
            num <- num + 1;
            change_do_children (SVD_aux (SVD_module m, Unique (num - 1, l)))
        | SVD_aux (SVD_fundef f, l) ->
            num <- num + 1;
            change_do_children (SVD_aux (SVD_fundef f, Unique (num - 1, l)))
        | _ -> DoChildren

      method! vstatement =
        function
        | SVS_aux (SVS_var (name, ctyp, init_opt), l) ->
            num <- num + 1;
            ChangeTo (SVS_aux (SVS_var (name, ctyp, init_opt), Unique (num - 1, l)))
        (* We also number blocks, to keep track of where variable uses occur *)
        | SVS_aux (SVS_block statements, l) ->
            num <- num + 1;
            change_do_children (SVS_aux (SVS_block statements, Unique (num - 1, l)))
        | _ -> DoChildren
    end

  class unnumber_var_visitor : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren

      method! vdef =
        function
        | SVD_aux (SVD_var (name, ctyp), Unique (_, l)) -> ChangeTo (SVD_aux (SVD_var (name, ctyp), l))
        | SVD_aux (SVD_module m, Unique (_, l)) -> ChangeTo (SVD_aux (SVD_module m, l))
        | SVD_aux (SVD_fundef f, Unique (_, l)) -> ChangeTo (SVD_aux (SVD_fundef f, l))
        | _ -> DoChildren

      method! vstatement =
        function
        | SVS_aux (SVS_var (name, ctyp, init_opt), Unique (_, l)) ->
            ChangeTo (SVS_aux (SVS_var (name, ctyp, init_opt), l))
        | SVS_aux (SVS_block statements, Unique (_, l)) -> change_do_children (SVS_aux (SVS_block statements, l))
        | _ -> DoChildren
    end

  let simplify_empty_block = function
    | SVS_aux (SVS_block stmts, l) when List.for_all is_skip stmts -> SVS_aux (SVS_skip, l)
    | no_change -> no_change

  let simplify_empty_always_comb = function
    | SVD_aux (SVD_always_comb (SVS_aux (SVS_skip, _)), l) -> SVD_aux (SVD_null, l)
    | no_change -> no_change

  type write_value = No_write | Single_write of smt_exp | Multi_write

  type usage = {
    mutable reads : int;
    mutable writes : int;
    (* If the variable is in the outputs of a module instantiation, we
       don't want to remove it. *)
    mutable outputs : int;
    (* If the variable is in the inputs or output list of a SVS_raw
       statement, likewise, we can't remove it. *)
    mutable raws : int;
    (* The variable might be propagated, in which case we can't remove
       it (at least within the same simplification pass). This means
       the variable appears in other variable's propagate_write_value
       fields. *)
    mutable propagated : int;
    (* A write value that can be propagated. A variable usage might
       have multiple writes (i.e. writes > 0), but none that can be
       propagated. *)
    mutable propagate_write_value : write_value;
    mutable locations : IntSet.t;
  }

  let single_write_value usage =
    usage.writes = 1 && usage.outputs = 0 && usage.raws = 0 && usage.propagated = 0
    && match usage.propagate_write_value with Single_write _ -> true | _ -> false

  let create_usage () =
    {
      reads = 0;
      writes = 0;
      outputs = 0;
      raws = 0;
      propagated = 0;
      propagate_write_value = No_write;
      locations = IntSet.empty;
    }

  let no_usage = create_usage ()

  type frame =
    | Block of int * (int * ctyp) NameMap.t
    | Foreach of Jib.name
    | Ports of NameSet.t
    | Function of NameSet.t

  type propagation_type = Forbid | Variable | Literal

  let combine x y =
    match (x, y) with
    | Forbid, _ -> Forbid
    | _, Forbid -> Forbid
    | Variable, _ -> Variable
    | _, Variable -> Variable
    | _ -> Literal

  let rec can_propagate stack name = function
    | Bitvec_lit _ | Bool_lit _ | String_lit _ | Member _ -> Literal
    | Fn ("=", [x; y]) -> combine (can_propagate stack name x) (can_propagate stack name y)
    | Fn ("not", [Fn ("=", [x; y])]) -> combine (can_propagate stack name x) (can_propagate stack name y)
    | Ite (i, t, e) ->
        combine (combine (can_propagate stack name i) (can_propagate stack name t)) (can_propagate stack name e)
    | Fn (("or" | "and"), xs) ->
        if List.for_all (fun x -> match can_propagate stack name x with Literal -> true | _ -> false) xs then Literal
        else if
          List.for_all (fun x -> match can_propagate stack name x with Literal | Variable -> true | _ -> false) xs
        then Variable
        else Forbid
    | Field (_, _, x) -> can_propagate stack name x
    | Unwrap (_, _, x) -> can_propagate stack name x
    | Var v ->
        let rec walk found = function
          | Block (_, vars) :: tail ->
              let found = found || NameMap.mem name vars in
              if NameMap.mem v vars then if found then Variable else Forbid else walk found tail
          | Foreach v' :: tail -> if Name.compare v v' = 0 then Literal else walk found tail
          | (Function args | Ports args) :: tail -> if NameSet.mem v args then Literal else walk found tail
          | [] -> Forbid
        in
        walk false stack
    | _ -> Forbid

  let add_var name num ctyp = function
    | Block (n, vars) :: tail -> Block (n, NameMap.add name (num, ctyp) vars) :: tail
    | stack -> stack

  let rec get_num ?first_block name = function
    | head :: tail -> begin
        match head with
        | Block (bnum, vars) -> begin
            let bnum = Option.value ~default:bnum first_block in
            match NameMap.find_opt name vars with
            | Some (vnum, ctyp) -> Some (bnum, vnum, ctyp)
            | None -> get_num ~first_block:bnum name tail
          end
        | Foreach var -> if Name.compare name var = 0 then None else get_num ?first_block name tail
        | Ports ports -> if NameSet.mem name ports then None else get_num ?first_block name tail
        | Function params -> if NameSet.mem name params then None else get_num ?first_block name tail
      end
    | [] -> None

  class remove_unused_visitor uses changes skip : svir_visitor =
    object (self)
      inherit empty_svir_visitor

      val mutable stack = [Block (-1, NameMap.empty)]

      method private push_frame frame = stack <- frame :: stack
      method private push bnum = stack <- Block (bnum, NameMap.empty) :: stack
      method private pop () = stack <- List.tl stack

      method private add_var name num ctyp = stack <- add_var name num ctyp stack

      method private get_vnum name = get_num name stack

      method! vctyp _ = SkipChildren

      method! vsmt_exp =
        function
        | Var name -> begin
            match self#get_vnum name with
            | Some (_, vnum, ctyp) ->
                let usage = Option.value ~default:no_usage (Hashtbl.find_opt uses vnum) in
                begin
                  match usage.propagate_write_value with
                  | Single_write exp ->
                      incr changes;
                      ChangeTo exp
                  | _ -> SkipChildren
                end
            | None -> SkipChildren
          end
        | _ -> DoChildren

      method! vplace =
        function
        | SVP_id name -> begin
            match self#get_vnum name with
            | Some (_, vnum, ctyp) ->
                let usage = Option.value ~default:no_usage (Hashtbl.find_opt uses vnum) in
                if usage.reads = 0 && usage.writes <= 1 && usage.outputs = 0 && usage.raws = 0 then
                  ChangeTo (SVP_void ctyp)
                else SkipChildren
            | None -> SkipChildren
          end
        | _ -> DoChildren

      method! vdef =
        function
        | SVD_aux (SVD_var (name, ctyp), Unique (vnum, l)) ->
            self#add_var name vnum ctyp;
            let usage = Option.value ~default:no_usage (Hashtbl.find_opt uses vnum) in
            if usage.reads = 0 && usage.writes <= 1 && usage.outputs = 0 && usage.raws = 0 then (
              incr changes;
              ChangeTo (SVD_aux (SVD_null, l))
            )
            else if single_write_value usage then (
              incr changes;
              ChangeTo (SVD_aux (SVD_null, l))
            )
            else DoChildren
        | SVD_aux (((SVD_module _ | SVD_fundef _) as aux), l) -> begin
            let frame =
              match aux with
              | SVD_fundef f ->
                  let paramset = List.fold_left (fun set (id, _) -> NameSet.add (name id) set) NameSet.empty f.params in
                  Function paramset
              | SVD_module m ->
                  let portset =
                    List.fold_left
                      (fun set (port : sv_module_port) -> NameSet.add port.name set)
                      NameSet.empty m.input_ports
                  in
                  let portset =
                    List.fold_left (fun set (port : sv_module_port) -> NameSet.add port.name set) portset m.output_ports
                  in
                  Ports portset
              | _ -> assert false
            in
            match l with
            | Unique (n, _) ->
                if Hashtbl.mem skip n then SkipChildren
                else (
                  let before_changes = !changes in
                  self#push_frame frame;
                  self#push n;
                  DoChildrenPost
                    (fun () ->
                      let after_changes = !changes in
                      if before_changes = after_changes then Hashtbl.add skip n ();
                      self#pop ();
                      self#pop ()
                    )
                )
            | _ -> Reporting.unreachable l __POS__ "Un-numbered module or function"
          end
        | SVD_aux (SVD_always_comb _, _) as comb -> ChangeDoChildrenPost (comb, simplify_empty_always_comb)
        | _ -> DoChildren

      method! vstatement =
        function
        | SVS_aux (SVS_var (name, ctyp, init_opt), Unique (vnum, l)) ->
            let usage = Option.value ~default:no_usage (Hashtbl.find_opt uses vnum) in
            if usage.reads = 0 && usage.writes <= 1 && usage.outputs = 0 && usage.raws = 0 then (
              incr changes;
              ChangeTo (SVS_aux (SVS_skip, l))
            )
            else if single_write_value usage then (
              incr changes;
              ChangeTo (SVS_aux (SVS_skip, l))
            )
            else DoChildren
        | SVS_aux (SVS_block _, Unique (bnum, _)) as block ->
            self#push bnum;
            ChangeDoChildrenPost
              ( block,
                fun block ->
                  self#pop ();
                  simplify_empty_block block
              )
        | SVS_aux (SVS_assign (SVP_id name, exp), l) as assign -> begin
            match can_propagate stack name exp with
            | Forbid ->
                ChangeDoChildrenPost
                  ( assign,
                    function SVS_aux (SVS_assign (SVP_void _, _), l) -> SVS_aux (SVS_skip, l) | assign -> assign
                  )
            | Literal | Variable -> begin
                match self#get_vnum name with
                | Some (_, vnum, _) ->
                    let usage = Option.value ~default:no_usage (Hashtbl.find_opt uses vnum) in
                    if usage.reads = 0 && usage.writes <= 1 && usage.outputs = 0 && usage.raws = 0 then
                      ChangeTo (SVS_aux (SVS_skip, l))
                    else if single_write_value usage then ChangeTo (SVS_aux (SVS_skip, l))
                    else DoChildren
                | None -> DoChildren
              end
          end
        | SVS_aux (SVS_assign _, _) as assign ->
            ChangeDoChildrenPost
              (assign, function SVS_aux (SVS_assign (SVP_void _, _), l) -> SVS_aux (SVS_skip, l) | assign -> assign)
        | SVS_aux (SVS_call _, _) as call ->
            ChangeDoChildrenPost
              (call, function SVS_aux (SVS_call (SVP_void _, _, _), l) -> SVS_aux (SVS_skip, l) | call -> call)
        | _ -> DoChildren
    end

  let push frame stack = stack := frame :: !stack

  let pop stack = stack := List.tl !stack

  let add_use ?(read = false) ?(write = false) ?(output = false) ?(raw = false) ?(propagated = false) ?write_value name
      stack uses =
    match get_num name !stack with
    | Some (bnum, vnum, _) ->
        let usage =
          match Hashtbl.find_opt uses vnum with
          | Some usage -> usage
          | None ->
              let usage = create_usage () in
              Hashtbl.add uses vnum usage;
              usage
        in
        if read then usage.reads <- usage.reads + 1;
        if write then usage.writes <- usage.writes + 1;
        if output then usage.outputs <- usage.outputs + 1;
        if raw then usage.raws <- usage.raws + 1;
        if propagated then usage.propagated <- usage.propagated + 1;
        usage.propagate_write_value <-
          ( match (usage.propagate_write_value, write_value) with
          | write, None -> write
          | No_write, Some write -> Single_write write
          | _, Some _ -> Multi_write
          );
        usage.locations <- IntSet.add bnum usage.locations
    | None -> ()

  let rec smt_uses ?(propagated = false) stack uses = function
    | Var name -> add_use ~read:true ~propagated name stack uses
    | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Unit | Member _ | Empty_list -> ()
    | SignExtend (_, _, exp)
    | ZeroExtend (_, _, exp)
    | Extract (_, _, _, exp)
    | Tester (_, exp)
    | Unwrap (_, _, exp)
    | Field (_, _, exp)
    | Hd (_, exp)
    | Tl (_, exp) ->
        smt_uses ~propagated stack uses exp
    | Ite (i, t, e) ->
        smt_uses ~propagated stack uses i;
        smt_uses ~propagated stack uses t;
        smt_uses ~propagated stack uses e
    | Fn (_, args) -> List.iter (smt_uses ~propagated stack uses) args
    | Store (_, _, arr, i, x) ->
        smt_uses ~propagated stack uses arr;
        smt_uses ~propagated stack uses i;
        smt_uses ~propagated stack uses x
    | Struct (_, fields) -> List.iter (fun (_, exp) -> smt_uses ~propagated stack uses exp) fields

  let rec place_uses ?(output = false) stack uses = function
    | SVP_id name -> add_use ~write:true ~output name stack uses
    | SVP_index (place, exp) ->
        place_uses ~output stack uses place;
        smt_uses stack uses exp
    | SVP_field (place, _) -> place_uses ~output stack uses place
    | SVP_multi places -> List.iter (place_uses ~output stack uses) places
    | SVP_void _ -> ()

  let rec statement_uses stack uses (SVS_aux (aux, l)) =
    match aux with
    | SVS_comment _ | SVS_skip | SVS_split_comb -> ()
    | SVS_var (name, ctyp, init_opt) ->
        begin
          match init_opt with Some init -> smt_uses stack uses init | None -> ()
        end;
        begin
          match l with Unique (num, _) -> stack := add_var name num ctyp !stack | _ -> ()
        end
    | SVS_block statements ->
        let bnum =
          match l with Unique (num, _) -> num | _ -> Reporting.unreachable l __POS__ "Un-numbered block found"
        in
        push (Block (bnum, NameMap.empty)) stack;
        List.iter (statement_uses stack uses) statements;
        pop stack
    | SVS_assign (SVP_id name, exp) -> begin
        match can_propagate !stack name exp with
        | Variable ->
            add_use ~write:true ~write_value:exp name stack uses;
            smt_uses ~propagated:true stack uses exp
        | Literal -> add_use ~write:true ~write_value:exp name stack uses
        | Forbid ->
            add_use ~write:true name stack uses;
            smt_uses stack uses exp
      end
    | SVS_assign (place, exp) | SVS_continuous_assign (place, exp) ->
        place_uses stack uses place;
        smt_uses stack uses exp
    | SVS_call (place, _, args) ->
        place_uses stack uses place;
        List.iter (smt_uses stack uses) args
    | SVS_if (cond, then_stmt_opt, else_stmt_opt) ->
        smt_uses stack uses cond;
        begin
          match then_stmt_opt with Some then_stmt -> statement_uses stack uses then_stmt | None -> ()
        end;
        begin
          match else_stmt_opt with Some else_stmt -> statement_uses stack uses else_stmt | None -> ()
        end
    | SVS_assert (cond, msg) ->
        smt_uses stack uses cond;
        smt_uses stack uses msg
    | SVS_case { head_exp; cases; fallthrough } ->
        smt_uses stack uses head_exp;
        List.iter (fun (_, stmt) -> statement_uses stack uses stmt) cases;
        begin
          match fallthrough with Some stmt -> statement_uses stack uses stmt | None -> ()
        end
    | SVS_foreach (_, exp, stmt) ->
        smt_uses stack uses exp;
        statement_uses stack uses stmt
    | SVS_for (_, stmt) -> statement_uses stack uses stmt
    | SVS_raw (_, inputs, outputs) ->
        List.iter (fun name -> add_use ~raw:true ~read:true name stack uses) inputs;
        List.iter (fun name -> add_use ~raw:true ~write:true name stack uses) outputs
    | SVS_return exp -> smt_uses stack uses exp

  let rec def_uses stack uses (SVD_aux (aux, l)) =
    match aux with
    | SVD_type _ | SVD_null | SVD_dpi_function _ -> ()
    | SVD_fundef { params; body; _ } ->
        let paramset = List.fold_left (fun set (id, _) -> NameSet.add (name id) set) NameSet.empty params in
        push (Function paramset) stack;
        statement_uses stack uses body;
        pop stack
    | SVD_module { input_ports; output_ports; defs; _ } ->
        let portset =
          List.fold_left (fun set (port : sv_module_port) -> NameSet.add port.name set) NameSet.empty input_ports
        in
        let portset =
          List.fold_left (fun set (port : sv_module_port) -> NameSet.add port.name set) portset output_ports
        in
        push (Ports portset) stack;
        defs_uses stack uses defs;
        pop stack
    | SVD_var (name, ctyp) -> begin match l with Unique (num, _) -> stack := add_var name num ctyp !stack | _ -> () end
    | SVD_instantiate { input_connections; output_connections; _ } ->
        List.iter (smt_uses stack uses) input_connections;
        List.iter (place_uses ~output:true stack uses) output_connections
    | SVD_always_comb stmt -> statement_uses stack uses stmt
    | SVD_initial stmt -> statement_uses stack uses stmt
    | SVD_always_ff stmt ->
        add_use ~raw:true ~read:true (name (mk_id "clk")) stack uses;
        statement_uses stack uses stmt

  and defs_uses stack uses defs =
    push (Block (-1, NameMap.empty)) stack;
    List.iter (def_uses stack uses) defs;
    pop stack

  let rewrite defs =
    let defs = visit_sv_defs (new number_var_visitor) defs in
    let skip = Hashtbl.create 4096 in
    let rec go defs =
      let changes = ref 0 in
      let uses = Hashtbl.create 4096 in
      defs_uses (ref []) uses defs;
      let defs = visit_sv_defs (new remove_unused_visitor uses changes skip) defs in
      let defs = SimpSMT.rewrite defs in
      if !changes > 0 then go defs else defs
    in
    let defs = go defs in
    visit_sv_defs (new unnumber_var_visitor) defs
end

let remove_unused_variables = profile_rewrite RemoveUnusedVariables.rewrite ~message:"Removing unused variables"

module CaseInsertion = struct
  let rec can_be_case = function
    | Ite (Fn ("=", [Var v; Bitvec_lit bv]), t, (Ite _ as e)) -> begin
        match can_be_case e with
        | None -> None
        | Some (n, v', cases, e) -> if Name.compare v v' = 0 then Some (n + 1, v, (bv, t) :: cases, e) else None
      end
    | Ite (Fn ("=", [Var v; Bitvec_lit bv]), t, e) -> Some (0, v, [(bv, t)], e)
    | exp -> None

  class case_insertion_visitor : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vstatement =
        function
        | SVS_aux (SVS_assign (place, exp), l) -> begin
            match can_be_case exp with
            | Some (n, v, cases, default) when n > 2 ->
                ChangeTo
                  (SVS_aux
                     ( SVS_case
                         {
                           head_exp = Var v;
                           cases =
                             List.map (fun (bv, exp) -> (Bitvec_lit bv, SVS_aux (SVS_assign (place, exp), l))) cases;
                           fallthrough = Some (SVS_aux (SVS_assign (place, default), l));
                         },
                       l
                     )
                  )
            | _ -> DoChildren
          end
        | _ -> DoChildren
    end

  let rewrite defs = visit_sv_defs (new case_insertion_visitor) defs
end

let insert_case_expressions = profile_rewrite CaseInsertion.rewrite ~message:"Inserting case expressions"
