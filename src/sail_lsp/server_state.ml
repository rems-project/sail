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

open Libsail

open Ast
open Ast_compare
open Ast_util
open Ast_defs

open Util.Result_monad

type parse_continuation = {
  check : Type_check.Env.t -> Type_check.typed_lazy_ast * Type_check.Env.t;
  vs_ids : IdSet.t;
  regs : (Ast.id * Ast.typ) list;
  symbols : Preprocess.symbol_set;
  ctx : Initial_check.ctx;
}

type parsed_file =
  | Generated of Parse_ast.def list
  | File of {
      id : Project.mod_id;
      handle : Sail_file.handle;
      cont : Preprocess.symbol_set -> Initial_check.ctx -> parse_continuation;
    }

type checked_ast = Full of Type_check.typed_ast | Lazy of Type_check.typed_lazy_ast

type checked_sequence =
  | Checked of {
      parsed : parsed_file;
      vs_ids : IdSet.t;
      regs : (Ast.id * Ast.typ) list;
      symbols : Preprocess.symbol_set;
      ctx : Initial_check.ctx;
      ast : checked_ast;
      env : Type_check.env;
      next : checked_sequence;
    }
  | Start

type state = {
  default_sail_dir : string;
  project : Project.project_structure;
  initial_env : Type_check.env;
  parsed : (parsed_file, Sail_file.handle * Reporting.error) Result.t list;
  checked : checked_sequence;
}

let last_vs_ids state = match state.checked with Start -> IdSet.empty | Checked c -> c.vs_ids

let last_symbols state = match state.checked with Start -> Preprocess.get_default_symbols () | Checked c -> c.symbols

let last_ctx state = match state.checked with Start -> Initial_check.initial_ctx | Checked c -> c.ctx

let last_regs state = match state.checked with Start -> [] | Checked c -> c.regs

let last_env state = match state.checked with Start -> state.initial_env | Checked c -> c.env

let force_last_ast state =
  match state.checked with
  | Start -> { defs = []; comments = [] }
  | Checked c -> (
      match c.ast with Full ast -> ast | Lazy lazy_ast -> force_lazy_ast lazy_ast
    )

let update_ast ast state =
  match state.checked with Start -> state | Checked c -> { state with checked = Checked { c with ast = Full ast } }

let parse_file ?loc ~default_sail_dir mod_id path =
  let handle = Sail_file.open_file path in
  let extension = Filename.extension (Sail_file.Path.to_string path) in
  let module Handler = (val Frontend.get_handler ~path extension : Frontend.FILE_HANDLER) in
  try
    let parsed = Handler.parse loc path in
    let cont symbols ctx =
      let processed, symbols, ctx =
        Handler.process ~target_name:None ~default_sail_dir ~options:[] ~symbols ctx parsed
      in
      {
        check = (fun env -> Handler.check_lazy env processed);
        vs_ids = Handler.defines_functions processed;
        regs = Handler.uninitialized_registers processed;
        symbols;
        ctx;
      }
    in
    Ok (File { id = mod_id; handle; cont })
  with Reporting.Fatal_error err -> Error (handle, err)

let reparse ?loc ~default_sail_dir mod_id handle =
  let path = Sail_file.to_path handle in
  let extension = Filename.extension (Sail_file.Path.to_string path) in
  let module Handler = (val Frontend.get_handler ~path extension : Frontend.FILE_HANDLER) in
  try
    let parsed = Handler.parse loc path in
    let cont symbols ctx =
      let processed, symbols, ctx =
        Handler.process ~target_name:None ~default_sail_dir ~options:[] ~symbols ctx parsed
      in
      {
        check = (fun env -> Handler.check_lazy env processed);
        vs_ids = Handler.defines_functions processed;
        regs = Handler.uninitialized_registers processed;
        symbols;
        ctx;
      }
    in
    Ok cont
  with Reporting.Fatal_error err -> Error err

let rec invalidate_checked state h =
  match state.checked with
  | Checked c -> (
      let next_state = { state with parsed = Ok c.parsed :: state.parsed; checked = c.next } in
      match c.parsed with
      | File { handle; _ } when Sail_file.handle_compare h handle = 0 -> Some next_state
      | _ -> invalidate_checked next_state h
    )
  | Start -> None

let invalidate state h =
  if
    List.exists
      (function
        | Ok (Generated _) -> false
        | Ok (File { handle; _ }) | Error (handle, _) -> Sail_file.handle_compare h handle = 0
        )
      state.parsed
  then Some state
  else invalidate_checked state h

let rec check_up_to state h =
  match state.parsed with
  | [] -> Ok state
  | Error (_, err) :: _ -> Error err
  | Ok (File { id = mod_id; handle; cont = _ } as p) :: rest ->
      let* cont = reparse ~default_sail_dir:state.default_sail_dir mod_id handle in
      let* s =
        try
          let processed = cont (last_symbols state) (last_ctx state) in
          let ast, env = processed.check (last_env state) in
          Ok
            {
              state with
              parsed = rest;
              checked =
                Checked
                  {
                    parsed = p;
                    vs_ids = IdSet.union processed.vs_ids (last_vs_ids state);
                    regs = last_regs state @ processed.regs;
                    symbols = processed.symbols;
                    ctx = processed.ctx;
                    ast = Lazy ast;
                    env;
                    next = state.checked;
                  };
            }
        with
        | Reporting.Fatal_error err -> Error err
        | Type_error.Type_error (l, err) ->
            let str, hint = Type_error.string_of_type_error err in
            Error (Reporting.Err_type (l, hint, str))
      in
      if Sail_file.handle_compare h handle = 0 then (
        try
          let ast = force_last_ast s in
          Ok (update_ast ast state)
        with
        | Reporting.Fatal_error err -> Error err
        | Type_error.Type_error (l, err) ->
            let str, hint = Type_error.string_of_type_error err in
            Error (Reporting.Err_type (l, hint, str))
      )
      else check_up_to s h
  | Ok (Generated defs as p) :: rest ->
      let defs, symbols =
        Preprocess.preprocess ~default_sail_dir:state.default_sail_dir ~target_name:None ~options:[]
          ~symbols:(last_symbols state) defs
      in
      let ast, ctx = Initial_check.process_ast (last_ctx state) (Parse_ast.Defs [(None, defs)]) in
      let ast, env = Type_check.check_lazy (last_env state) ast in
      let next_state =
        {
          state with
          parsed = rest;
          checked =
            Checked
              {
                parsed = p;
                vs_ids = last_vs_ids state;
                regs = last_regs state;
                symbols;
                ctx;
                ast = Lazy ast;
                env;
                next = state.checked;
              };
        }
      in
      check_up_to next_state h

let wrap_module proj mod_id files =
  let module P = Parse_ast in
  let open Project in
  let name, l = module_name proj mod_id in
  let bracket_pragma p = [Ok (Generated [P.DEF_aux (P.DEF_pragma (p, P.Pragma_line (name, 1)), to_loc l)])] in
  bracket_pragma "start_module#" @ files @ bracket_pragma "end_module#"

let load_modules ~default_sail_dir proj =
  let open Project in
  let env = Type_check.initial_env_with_modules proj in
  let mod_ids = module_order proj in

  let parsed_modules =
    List.concat_map
      (fun mod_id ->
        let files = module_files proj mod_id in
        List.map (fun (path, l) -> parse_file ~loc:(Project.to_loc l) ~default_sail_dir mod_id path) files
        |> wrap_module proj mod_id
      )
      mod_ids
  in

  { default_sail_dir; initial_env = env; project = proj; parsed = parsed_modules; checked = Start }

let load_project ?(no_core = false) ?(variables = ref Util.StringMap.empty) ~default_sail_dir project_files =
  let project_files = List.map Sail_file.Path.actual project_files in
  let project_files = if no_core then project_files else Corelib_project.path :: project_files in

  let defs =
    List.map
      (fun project_file ->
        let root_directory = Filename.dirname (Sail_file.Path.to_string project_file) in
        Project.mk_root root_directory :: Initial_check.parse_project project_file
      )
      project_files
    |> List.concat
  in
  let proj = Project.initialize_project_structure ~variables defs in
  load_modules ~default_sail_dir proj
