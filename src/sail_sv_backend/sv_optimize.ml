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

open Jib
open Jib_util
open Jib_visitor
open Smt_exp
open Sv_ir

module IntMap = Util.IntMap

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
        | SVD_aux (SVD_module { name; input_ports; output_ports; defs }, l) ->
            port_actions := SVNameMap.add name (scan_ports input_ports, scan_ports output_ports) !port_actions;
            let unit_inputs, input_ports = List.partition is_unit_port input_ports in
            let unit_outputs, output_ports = List.partition is_unit_port output_ports in
            SVD_aux
              ( SVD_module
                  {
                    name;
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

let remove_unit_ports defs = RemoveUnitPorts.rewrite defs

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
        | _ -> DoChildren

      method! vstatement =
        function
        | SVS_aux (SVS_var (name, ctyp, init_opt), l) ->
            num <- num + 1;
            ChangeTo (SVS_aux (SVS_var (name, ctyp, init_opt), Unique (num - 1, l)))
        | _ -> DoChildren
    end

  class remove_unused_visitor uses : svir_visitor =
    object
      inherit empty_svir_visitor

      method! vctyp _ = SkipChildren
      method! vplace _ = SkipChildren
      method! vsmt_exp _ = SkipChildren

      method! vdef =
        function
        | SVD_aux (SVD_var (name, ctyp), Unique (vnum, l)) -> begin
            match IntMap.find_opt vnum uses with
            | Some count when count > 0 -> ChangeTo (SVD_aux (SVD_var (name, ctyp), l))
            | _ -> ChangeTo (SVD_aux (SVD_null, l))
          end
        | _ -> DoChildren

      method! vstatement =
        function
        | SVS_aux (SVS_var (name, ctyp, init_opt), Unique (vnum, l)) -> begin
            match IntMap.find_opt vnum uses with
            | Some count when count > 0 -> ChangeTo (SVS_aux (SVS_var (name, ctyp, init_opt), l))
            | _ -> ChangeTo (SVS_aux (SVS_skip, l))
          end
        | _ -> DoChildren
    end

  type frame = Block of int NameMap.t | Foreach of Jib.name | Ports of NameSet.t | Function of NameSet.t

  let add_var name num = function Block head :: tail -> Block (NameMap.add name num head) :: tail | stack -> stack

  let rec get_num name = function
    | head :: tail -> begin
        match head with
        | Block vars -> begin
            match NameMap.find_opt name vars with Some num -> Some num | None -> get_num name tail
          end
        | Foreach var -> if Name.compare name var = 0 then None else get_num name tail
        | Ports ports -> if NameSet.mem name ports then None else get_num name tail
        | Function params -> if NameSet.mem name params then None else get_num name tail
      end
    | [] -> None

  let push frame stack = stack := frame :: !stack

  let pop stack = stack := List.tl !stack

  let rec smt_uses stack uses = function
    | Var name -> begin
        match get_num name !stack with
        | Some num -> uses := IntMap.update num (function None -> Some 1 | Some count -> Some (count + 1)) !uses
        | None -> ()
      end
    | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Unit | Member _ | Empty_list -> ()
    | SignExtend (_, _, exp)
    | ZeroExtend (_, _, exp)
    | Extract (_, _, exp)
    | Tester (_, exp)
    | Unwrap (_, _, exp)
    | Field (_, _, exp)
    | Hd (_, exp)
    | Tl (_, exp) ->
        smt_uses stack uses exp
    | Ite (i, t, e) ->
        smt_uses stack uses i;
        smt_uses stack uses t;
        smt_uses stack uses e
    | Fn (_, args) -> List.iter (smt_uses stack uses) args
    | Store (_, _, arr, i, x) ->
        smt_uses stack uses arr;
        smt_uses stack uses i;
        smt_uses stack uses x

  let rec place_uses stack uses = function
    | SVP_id name -> begin
        match get_num name !stack with
        | Some num -> uses := IntMap.update num (function None -> Some 1 | Some count -> Some (count + 1)) !uses
        | None -> ()
      end
    | SVP_index (place, exp) ->
        place_uses stack uses place;
        smt_uses stack uses exp
    | SVP_field (place, _) -> place_uses stack uses place
    | SVP_multi places -> List.iter (place_uses stack uses) places
    | SVP_void _ -> ()

  let rec statement_uses stack uses (SVS_aux (aux, l)) =
    match aux with
    | SVS_comment _ | SVS_skip | SVS_split_comb -> ()
    | SVS_var (name, _, init_opt) ->
        begin
          match init_opt with Some init -> smt_uses stack uses init | None -> ()
        end;
        begin
          match l with Unique (num, _) -> stack := add_var name num !stack | _ -> ()
        end
    | SVS_block statements ->
        push (Block NameMap.empty) stack;
        List.iter (statement_uses stack uses) statements;
        pop stack
    | SVS_assign (place, exp) ->
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
    | SVS_raw (_, inputs, outputs) ->
        List.iter
          (fun name ->
            match get_num name !stack with
            | Some num -> uses := IntMap.update num (function None -> Some 1 | Some count -> Some (count + 1)) !uses
            | None -> ()
          )
          (inputs @ outputs)
    | SVS_return exp -> smt_uses stack uses exp

  let rec def_uses stack uses (SVD_aux (aux, l)) =
    match aux with
    | SVD_type _ | SVD_null -> ()
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
    | SVD_var (name, _) -> begin match l with Unique (num, _) -> stack := add_var name num !stack | _ -> () end
    | SVD_instantiate { input_connections; output_connections; _ } ->
        List.iter (smt_uses stack uses) input_connections;
        List.iter (place_uses stack uses) output_connections
    | SVD_always_comb stmt -> statement_uses stack uses stmt

  and defs_uses stack uses defs =
    push (Block NameMap.empty) stack;
    List.iter (def_uses stack uses) defs;
    pop stack

  let rewrite defs =
    let defs = visit_sv_defs (new number_var_visitor) defs in
    let uses = ref IntMap.empty in
    defs_uses (ref []) uses defs;
    visit_sv_defs (new remove_unused_visitor !uses) defs
end

let remove_unused_variables = RemoveUnusedVariables.rewrite
