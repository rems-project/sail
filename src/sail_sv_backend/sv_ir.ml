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
open Jib_util
open Jib_visitor
open PPrint
open Smt_exp

type sv_name = SVN_id of Ast.id | SVN_string of string

module SVName = struct
  type t = sv_name
  let compare n1 n2 =
    match (n1, n2) with
    | SVN_id id1, SVN_id id2 -> Id.compare id1 id2
    | SVN_string s1, SVN_string s2 -> String.compare s1 s2
    | SVN_id _, _ -> 1
    | _, SVN_id _ -> -1
end

let modify_sv_name ?(prefix = "") ?(suffix = "") = function
  | SVN_id id -> SVN_id (append_id (prepend_id prefix id) suffix)
  | SVN_string str -> SVN_string (prefix ^ str ^ suffix)

let string_of_sv_name = function SVN_id id -> string_of_id id | SVN_string str -> str

module SVNameMap = Map.Make (SVName)

type sv_module_port = { name : Jib.name; external_name : string; typ : Jib.ctyp }

let mk_port name ctyp = { name; external_name = ""; typ = ctyp }

type sv_module = {
  name : sv_name;
  recursive : bool;
  input_ports : sv_module_port list;
  output_ports : sv_module_port list;
  defs : sv_def list;
}

and sv_function = {
  function_name : sv_name;
  return_type : Jib.ctyp option;
  params : (Ast.id * Jib.ctyp) list;
  body : sv_statement;
}

and sv_def = SVD_aux of sv_def_aux * Ast.l

and sv_def_aux =
  | SVD_null
  | SVD_type of Jib.ctype_def
  | SVD_module of sv_module
  | SVD_var of Jib.name * Jib.ctyp
  | SVD_fundef of sv_function
  | SVD_instantiate of {
      module_name : sv_name;
      instance_name : string;
      input_connections : smt_exp list;
      output_connections : sv_place list;
    }
  | SVD_always_comb of sv_statement
  | SVD_initial of sv_statement
  | SVD_always_ff of sv_statement
  | SVD_dpi_function of { function_name : sv_name; return_type : Jib.ctyp option; param_types : Jib.ctyp list }

and sv_place =
  | SVP_id of Jib.name
  | SVP_index of sv_place * smt_exp
  | SVP_field of sv_place * Ast.id
  | SVP_multi of sv_place list
  | SVP_void of Jib.ctyp

and sv_for_modifier = SVF_increment of Jib.name | SVF_decrement of Jib.name

and sv_for = { for_var : Jib.name * Jib.ctyp * smt_exp; for_cond : smt_exp; for_modifier : sv_for_modifier }

and sv_statement = SVS_aux of sv_statement_aux * Ast.l

and sv_statement_aux =
  | SVS_comment of string
  | SVS_skip
  | SVS_split_comb
  | SVS_var of Jib.name * Jib.ctyp * smt_exp option
  | SVS_return of smt_exp
  | SVS_assign of sv_place * smt_exp
  | SVS_continuous_assign of sv_place * smt_exp
  | SVS_call of sv_place * sv_name * smt_exp list
  | SVS_case of { head_exp : smt_exp; cases : (smt_exp * sv_statement) list; fallthrough : sv_statement option }
  | SVS_if of smt_exp * sv_statement option * sv_statement option
  | SVS_block of sv_statement list
  | SVS_assert of smt_exp * smt_exp
  | SVS_foreach of sv_name * smt_exp * sv_statement
  | SVS_for of sv_for * sv_statement
  | SVS_raw of string * Jib.name list * Jib.name list

let filter_skips = List.filter (function SVS_aux (SVS_skip, _) -> false | _ -> true)

let is_split_comb = function SVS_aux (SVS_split_comb, _) -> true | _ -> false

let is_null_def = function SVD_aux (SVD_null, _) -> true | _ -> false

let is_skip = function SVS_aux (SVS_skip, _) -> true | _ -> false

let svs_block stmts = SVS_block (filter_skips stmts)

let svs_raw ?(inputs = []) ?(outputs = []) s = SVS_raw (s, inputs, outputs)

let mk_def ?(loc = Parse_ast.Unknown) aux = SVD_aux (aux, loc)

let mk_statement ?(loc = Parse_ast.Unknown) aux = SVS_aux (aux, loc)

let is_typedef = function SVD_aux (SVD_type _, _) -> true | _ -> false

class type svir_visitor = object
  inherit common_visitor
  method vsmt_exp : smt_exp -> smt_exp visit_action
  method vplace : sv_place -> sv_place visit_action
  method vstatement : sv_statement -> sv_statement visit_action
  method vdef : sv_def -> sv_def visit_action
end

let rec visit_smt_exp (vis : svir_visitor) outer_smt_exp =
  let aux (vis : svir_visitor) no_change =
    match no_change with
    | Var name ->
        let name' = visit_name (vis :> common_visitor) name in
        if name == name' then no_change else Var name'
    | ZeroExtend (n, m, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else ZeroExtend (n, m, exp')
    | SignExtend (n, m, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else SignExtend (n, m, exp')
    | Extract (n, m, len, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Extract (n, m, len, exp')
    | Hd (hd_op, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Hd (hd_op, exp')
    | Tl (tl_op, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Tl (tl_op, exp')
    | Tester (test, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Tester (test, exp')
    | Ite (i, t, e) ->
        let i' = visit_smt_exp vis i in
        let t' = visit_smt_exp vis t in
        let e' = visit_smt_exp vis e in
        if i == i' && t == t' && e == e' then no_change else Ite (i', t', e')
    | Store (info, store_fn, arr, index, x) ->
        let arr' = visit_smt_exp vis arr in
        let index' = visit_smt_exp vis index in
        let x' = visit_smt_exp vis x in
        if arr == arr' && index == index' && x == x' then no_change else Store (info, store_fn, arr', index', x')
    | Field (struct_id, field_id, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Field (struct_id, field_id, exp')
    | Struct (struct_id, fields) ->
        let fields' = map_no_copy (fun (field_id, exp) -> (field_id, visit_smt_exp vis exp)) fields in
        if fields == fields' then no_change else Struct (struct_id, fields)
    | Fn (f, args) ->
        let args' = map_no_copy (visit_smt_exp vis) args in
        if args == args' then no_change else Fn (f, args')
    | Unwrap (ctor, b, exp) ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else Unwrap (ctor, b, exp')
    | Bool_lit _ | Bitvec_lit _ | Real_lit _ | String_lit _ | Unit | Member _ | Empty_list -> no_change
  in
  do_visit vis (vis#vsmt_exp outer_smt_exp) aux outer_smt_exp

let rec visit_sv_place (vis : svir_visitor) outer_place =
  let aux (vis : svir_visitor) no_change =
    match no_change with
    | SVP_id name ->
        let name' = visit_name (vis :> common_visitor) name in
        if name == name' then no_change else SVP_id name'
    | SVP_index (place, exp) ->
        let place' = visit_sv_place vis place in
        let exp' = visit_smt_exp vis exp in
        if place == place' && exp == exp' then no_change else SVP_index (place', exp')
    | SVP_field (place, field_id) ->
        let place' = visit_sv_place vis place in
        if place == place' then no_change else SVP_field (place', field_id)
    | SVP_multi places ->
        let places' = map_no_copy (visit_sv_place vis) places in
        if places == places' then no_change else SVP_multi places'
    | SVP_void ctyp ->
        let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
        if ctyp == ctyp' then no_change else SVP_void ctyp'
  in
  do_visit vis (vis#vplace outer_place) aux outer_place

let rec visit_sv_statement (vis : svir_visitor) outer_statement =
  let aux (vis : svir_visitor) (SVS_aux (stmt, l) as no_change) =
    match stmt with
    | SVS_var (name, ctyp, None) ->
        let name' = visit_name (vis :> common_visitor) name in
        let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
        if name == name' && ctyp == ctyp' then no_change else SVS_aux (SVS_var (name', ctyp', None), l)
    | SVS_var (name, ctyp, Some exp) ->
        let name' = visit_name (vis :> common_visitor) name in
        let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
        let exp' = visit_smt_exp vis exp in
        if name == name' && ctyp == ctyp' && exp == exp' then no_change
        else SVS_aux (SVS_var (name', ctyp', Some exp'), l)
    | SVS_assign (place, exp) ->
        let place' = visit_sv_place vis place in
        let exp' = visit_smt_exp vis exp in
        if place == place' && exp == exp' then no_change else SVS_aux (SVS_assign (place', exp'), l)
    | SVS_continuous_assign (place, exp) ->
        let place' = visit_sv_place vis place in
        let exp' = visit_smt_exp vis exp in
        if place == place' && exp == exp' then no_change else SVS_aux (SVS_continuous_assign (place', exp'), l)
    | SVS_block statements ->
        let statements' = map_no_copy (visit_sv_statement vis) statements in
        if statements == statements' then no_change else SVS_aux (SVS_block statements', l)
    | SVS_return exp ->
        let exp' = visit_smt_exp vis exp in
        if exp == exp' then no_change else SVS_aux (SVS_return exp', l)
    | SVS_call (place, f, args) ->
        let place' = visit_sv_place vis place in
        let args' = map_no_copy (visit_smt_exp vis) args in
        if place == place' && args == args' then no_change else SVS_aux (SVS_call (place', f, args'), l)
    | SVS_case { head_exp; cases; fallthrough } ->
        let head_exp' = visit_smt_exp vis head_exp in
        let cases' =
          map_no_copy
            (function
              | (exp, stmt) as no_change ->
                  let exp' = visit_smt_exp vis exp in
                  let stmt' = visit_sv_statement vis stmt in
                  if exp == exp' && stmt == stmt' then no_change else (exp', stmt')
              )
            cases
        in
        let fallthrough' = map_no_copy_opt (visit_sv_statement vis) fallthrough in
        if head_exp == head_exp' && cases == cases' && fallthrough == fallthrough' then no_change
        else SVS_aux (SVS_case { head_exp = head_exp'; cases = cases'; fallthrough = fallthrough' }, l)
    | SVS_assert (cond, msg) ->
        let cond' = visit_smt_exp vis cond in
        let msg' = visit_smt_exp vis msg in
        if cond == cond' && msg == msg' then no_change else SVS_aux (SVS_assert (cond', msg'), l)
    | SVS_foreach (i, exp, stmt) ->
        let exp' = visit_smt_exp vis exp in
        let stmt' = visit_sv_statement vis stmt in
        if exp == exp' && stmt == stmt' then no_change else SVS_aux (SVS_foreach (i, exp', stmt'), l)
    | SVS_for ({ for_var = v, ctyp, init; for_cond; for_modifier }, stmt) ->
        let v' = visit_name (vis :> common_visitor) v in
        let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
        let init' = visit_smt_exp vis init in
        let for_cond' = visit_smt_exp vis for_cond in
        let stmt' = visit_sv_statement vis stmt in
        if v == v' && ctyp == ctyp' && init == init' && for_cond == for_cond' && stmt == stmt' then no_change
        else SVS_aux (SVS_for ({ for_var = (v', ctyp', init'); for_cond = for_cond'; for_modifier }, stmt'), l)
    | SVS_if (exp, then_stmt_opt, else_stmt_opt) ->
        let exp' = visit_smt_exp vis exp in
        let then_stmt_opt' = map_no_copy_opt (visit_sv_statement vis) then_stmt_opt in
        let else_stmt_opt' = map_no_copy_opt (visit_sv_statement vis) else_stmt_opt in
        if exp == exp' && then_stmt_opt == then_stmt_opt' && else_stmt_opt == else_stmt_opt' then no_change
        else SVS_aux (SVS_if (exp', then_stmt_opt', else_stmt_opt'), l)
    | SVS_raw _ | SVS_comment _ | SVS_skip | SVS_split_comb -> no_change
  in
  do_visit vis (vis#vstatement outer_statement) aux outer_statement

let rec visit_sv_def (vis : svir_visitor) outer_def =
  let aux (vis : svir_visitor) (SVD_aux (def, l) as no_change) =
    match def with
    | SVD_null -> no_change
    | SVD_type _ -> no_change
    | SVD_module { name; recursive; input_ports; output_ports; defs } ->
        let visit_port ({ name; external_name; typ } as no_change) =
          let name' = visit_name (vis :> common_visitor) name in
          let typ' = visit_ctyp (vis :> common_visitor) typ in
          if name == name' && typ == typ' then no_change else { name = name'; external_name; typ = typ' }
        in
        let input_ports' = map_no_copy visit_port input_ports in
        let output_ports' = map_no_copy visit_port output_ports in
        let defs' = map_no_copy (visit_sv_def vis) defs in
        if input_ports == input_ports' && output_ports == output_ports' && defs == defs' then no_change
        else
          SVD_aux
            (SVD_module { name; recursive; input_ports = input_ports'; output_ports = output_ports'; defs = defs' }, l)
    | SVD_var (name, ctyp) ->
        let name' = visit_name (vis :> common_visitor) name in
        let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
        if name == name' && ctyp == ctyp' then no_change else SVD_aux (SVD_var (name', ctyp'), l)
    | SVD_instantiate { module_name; instance_name; input_connections; output_connections } ->
        let input_connections' = map_no_copy (visit_smt_exp vis) input_connections in
        let output_connections' = map_no_copy (visit_sv_place vis) output_connections in
        if input_connections == input_connections' && output_connections == output_connections' then no_change
        else
          SVD_aux
            ( SVD_instantiate
                {
                  module_name;
                  instance_name;
                  input_connections = input_connections';
                  output_connections = output_connections';
                },
              l
            )
    | SVD_fundef { function_name; return_type; params; body } ->
        let return_type' = map_no_copy_opt (visit_ctyp (vis :> common_visitor)) return_type in
        let params' =
          map_no_copy
            (function
              | (id, ctyp) as no_change ->
                  let ctyp' = visit_ctyp (vis :> common_visitor) ctyp in
                  if ctyp == ctyp' then no_change else (id, ctyp')
              )
            params
        in
        let body' = visit_sv_statement vis body in
        if return_type == return_type' && params == params' && body == body' then no_change
        else SVD_aux (SVD_fundef { function_name; return_type = return_type'; params = params'; body = body' }, l)
    | SVD_always_comb statement ->
        let statement' = visit_sv_statement vis statement in
        if statement == statement' then no_change else SVD_aux (SVD_always_comb statement', l)
    | SVD_initial statement ->
        let statement' = visit_sv_statement vis statement in
        if statement == statement' then no_change else SVD_aux (SVD_initial statement', l)
    | SVD_always_ff statement ->
        let statement' = visit_sv_statement vis statement in
        if statement == statement' then no_change else SVD_aux (SVD_always_ff statement', l)
    | SVD_dpi_function { function_name; return_type; param_types } ->
        let return_type' = map_no_copy_opt (visit_ctyp (vis :> common_visitor)) return_type in
        let param_types' = map_no_copy (visit_ctyp (vis :> common_visitor)) param_types in
        if return_type == return_type' && param_types = param_types' then no_change
        else SVD_aux (SVD_dpi_function { function_name; return_type = return_type'; param_types = param_types' }, l)
  in
  do_visit vis (vis#vdef outer_def) aux outer_def

let visit_sv_defs vis defs = map_no_copy (visit_sv_def vis) defs

class empty_svir_visitor : svir_visitor =
  object
    method vid _ = None
    method vname _ = None
    method vctyp _ = DoChildren
    method vsmt_exp _ = DoChildren
    method vplace _ = DoChildren
    method vstatement _ = DoChildren
    method vdef _ = DoChildren
  end
