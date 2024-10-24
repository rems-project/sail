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

open Ast_util
open Ast_defs

module StringMap = Map.Make (String)

let opt_ddump_initial_ast = ref false
let opt_ddump_side_effect = ref false
let opt_ddump_tc_ast = ref false
let opt_list_files = ref false
let opt_reformat : string option ref = ref None

let finalize_ast asserts_termination ctx env ast =
  Lint.warn_unmodified_variables ast;
  let ast = Scattered.descatter ast in
  let side_effects = Effects.infer_side_effects asserts_termination ast in
  if !opt_ddump_side_effect then Effects.dump_effects side_effects;
  Effects.check_side_effects side_effects ast;
  if !opt_ddump_tc_ast then Pretty_print_sail.output_ast stdout (Type_check.strip_ast ast);
  (ctx, ast, Type_check.Env.open_all_modules env, side_effects)

let instantiate_abstract_types tgt insts ast =
  let open Ast in
  let instantiate = function
    | DEF_aux (DEF_type (TD_aux (TD_abstract (id, kind), (l, _))), def_annot) as def -> begin
        match Bindings.find_opt id insts with
        | Some arg_fun ->
            let arg = arg_fun (unaux_kind kind) in
            DEF_aux
              ( DEF_type (TD_aux (TD_abbrev (id, mk_empty_typquant ~loc:(gen_loc l), arg), (l, Type_check.empty_tannot))),
                def_annot
              )
        | None -> def
      end
    | def -> def
  in
  let defs = List.map instantiate ast.defs in
  if Option.fold ~none:true ~some:Target.supports_abstract_types tgt then { ast with defs }
  else (
    match List.find_opt (function DEF_aux (DEF_type (TD_aux (TD_abstract _, _)), _) -> true | _ -> false) defs with
    | Some (DEF_aux (_, def_annot)) ->
        let target_name = Option.get tgt |> Target.name in
        raise
          (Reporting.err_general def_annot.loc
             (Printf.sprintf
                "Abstract types must be removed using the --instantiate option when generating code for target '%s'"
                target_name
             )
          )
    | None -> { ast with defs }
  )

type parse_continuation = {
  check : Type_check.Env.t -> Type_check.typed_ast * Type_check.Env.t;
  vs_ids : IdSet.t;
  regs : (Ast.id * Ast.typ) list;
  ctx : Initial_check.ctx;
}

type parsed_file =
  | Generated of Parse_ast.def list
  | File of { filename : string; cont : Initial_check.ctx -> parse_continuation }

type parsed_module = { id : Project.mod_id; included : bool; files : parsed_file list }

type processed_file =
  | ProcessedGenerated of untyped_def list
  | ProcessedFile of { filename : string; cont : Type_check.Env.t -> Type_check.typed_ast * Type_check.Env.t }

let wrap_module proj parsed_module =
  let module P = Parse_ast in
  let open Project in
  let name, l = module_name proj parsed_module.id in
  let bracket_pragma p = [Generated [P.DEF_aux (P.DEF_pragma (p, name, 1), to_loc l)]] in
  { parsed_module with files = bracket_pragma "start_module#" @ parsed_module.files @ bracket_pragma "end_module#" }

let filter_modules proj is_included ast =
  let open Ast in
  let get_module_id l name =
    match Project.get_module_id proj name with
    | Some mod_id -> mod_id
    | None -> Reporting.unreachable l __POS__ "Failed to get module id"
  in
  let rec go skipping acc = function
    | DEF_aux (DEF_pragma ("ended_module#", name, l), def_annot) :: defs ->
        let mod_id = get_module_id l name in
        begin
          match skipping with Some skip_id when mod_id = skip_id -> go None acc defs | _ -> go skipping acc defs
        end
    | _ :: defs when Option.is_some skipping -> go skipping acc defs
    | DEF_aux (DEF_pragma ("started_module#", name, l), def_annot) :: defs ->
        let mod_id = get_module_id l name in
        if is_included mod_id then go None acc defs else go (Some mod_id) acc defs
    | def :: defs -> go None (def :: acc) defs
    | [] -> List.rev acc
  in
  { ast with defs = go None [] ast.defs }

module type FILE_HANDLER = sig
  type parsed

  type processed

  val parse : Parse_ast.l option -> string -> parsed

  val defines_functions : processed -> IdSet.t

  val uninitialized_registers : processed -> (Ast.id * Ast.typ) list

  val process :
    default_sail_dir:string ->
    target_name:string option ->
    options:(Arg.key * Arg.spec * Arg.doc) list ->
    Initial_check.ctx ->
    parsed ->
    processed * Initial_check.ctx

  val check : Type_check.Env.t -> processed -> Type_check.typed_ast * Type_check.Env.t
end

module SailHandler : FILE_HANDLER = struct
  type parsed = string * Lexer.comment list * Parse_ast.def list

  type processed = untyped_ast

  let parse loc filename =
    let comments, defs = Initial_check.parse_file ?loc filename in
    (filename, comments, defs)

  let defines_functions ast = val_spec_ids ast.defs

  let uninitialized_registers ast = Initial_check.get_uninitialized_registers ast.defs

  let process ~default_sail_dir ~target_name ~options ctx (filename, comments, defs) =
    let defs = Preprocess.preprocess default_sail_dir target_name options defs in
    let ast, ctx = Initial_check.process_ast ctx (Parse_ast.Defs [(filename, defs)]) in
    ({ ast with comments = [(filename, comments)] }, ctx)

  let check env ast = Type_error.check env ast
end

let handlers : (string, (module FILE_HANDLER)) Hashtbl.t = Hashtbl.create 8

let register_file_handler ~extension handler = Hashtbl.replace handlers extension handler

let get_handler ~filename = function
  | ".sail" -> (module SailHandler : FILE_HANDLER)
  | extension -> (
      match Hashtbl.find_opt handlers extension with
      | Some h -> h
      | None ->
          raise
            (Reporting.err_general Parse_ast.Unknown
               (Printf.sprintf "No handler for file '%s' with extension '%s'" filename extension)
            )
    )

let parse_file ?loc ~target_name ~default_sail_dir ~options filename =
  let extension = Filename.extension filename in
  let module Handler = (val get_handler ~filename extension : FILE_HANDLER) in
  let parsed = Handler.parse loc filename in
  let cont ctx =
    let processed, ctx = Handler.process ~target_name ~default_sail_dir ~options ctx parsed in
    {
      check = (fun env -> Handler.check env processed);
      vs_ids = Handler.defines_functions processed;
      regs = Handler.uninitialized_registers processed;
      ctx;
    }
  in
  File { filename; cont }

let process_files ~target_name ~default_sail_dir ~options ctx vs_ids regs files =
  Util.fold_left_map
    (fun (ctx, vs_ids, regs) -> function
      | File { filename; cont } ->
          let cont = cont ctx in
          ((cont.ctx, IdSet.union vs_ids cont.vs_ids, regs @ cont.regs), ProcessedFile { filename; cont = cont.check })
      | Generated defs ->
          let defs = Preprocess.preprocess default_sail_dir target_name options defs in
          let ast, ctx = Initial_check.process_ast ctx (Parse_ast.Defs [("", defs)]) in
          ((ctx, vs_ids, regs), ProcessedGenerated ast.defs)
    )
    (ctx, vs_ids, regs) files

let check_files env files =
  Util.fold_left_map
    (fun env -> function
      | ProcessedFile { cont; _ } ->
          let ast, env = cont env in
          (env, ast)
      | ProcessedGenerated defs ->
          let defs, env = Type_error.check_defs env defs in
          (env, { defs; comments = [] })
    )
    env files

let load_modules ?target default_sail_dir options env proj root_mod_ids =
  let open Project in
  let mod_ids = module_order proj in
  let is_included = required_modules proj ~roots:(ModSet.of_list root_mod_ids) in

  let target_name = Option.map Target.name target in
  let asserts_termination = Option.fold ~none:false ~some:Target.asserts_termination target in

  let parsed_modules =
    List.map
      (fun mod_id ->
        let files = module_files proj mod_id in
        {
          id = mod_id;
          included = is_included mod_id;
          files =
            List.map
              (fun (filename, l) -> parse_file ~loc:(Project.to_loc l) ~target_name ~default_sail_dir ~options filename)
              files;
        }
      )
      mod_ids
  in

  if !opt_list_files then (
    let included_files =
      List.map (fun parsed_module -> if parsed_module.included then parsed_module.files else []) parsed_modules
      |> List.concat
    in
    print_endline
      (Util.string_of_list " "
         (fun s -> s)
         (List.filter_map (function File { filename; _ } -> Some filename | Generated _ -> None) included_files)
      );
    exit 0
  );

  let all_files =
    List.map (fun m -> m.files) parsed_modules
    |> List.concat
    |> List.filter_map (function File { filename; _ } -> Some filename | Generated _ -> None)
  in
  Option.iter (fun t -> Target.run_pre_initial_check_hook t all_files) target;

  let (ctx, vs_ids, regs), processed =
    let mods = List.map (wrap_module proj) parsed_modules in
    Util.fold_left_map
      (fun (ctx, vs_ids, regs) parsed_module ->
        let (ctx, vs_ids, regs), processed =
          process_files ~target_name ~default_sail_dir ~options ctx vs_ids regs parsed_module.files
        in
        (* If the module isn't being included we don't want to generate things for it's registers *)
        ((ctx, vs_ids, if is_included parsed_module.id then regs else []), processed)
      )
      (Initial_check.initial_ctx, IdSet.empty, [])
      mods
  in
  let processed =
    [ProcessedGenerated (Initial_check.generate_undefineds vs_ids)]
    @ List.concat processed
    @ [ProcessedGenerated (Initial_check.generate_initialize_registers vs_ids regs)]
  in

  let t = Profile.start () in
  let env, checked = check_files env processed in
  Profile.finish "type checking" t;

  let ast = concat_ast checked in
  let ast = filter_modules proj is_included ast in
  finalize_ast asserts_termination ctx env ast

let load_files ?target default_sail_dir options env files =
  let target_name = Option.map Target.name target in
  let asserts_termination = Option.fold ~none:false ~some:Target.asserts_termination target in

  let parsed_files = List.map (fun filename -> parse_file ~target_name ~default_sail_dir ~options filename) files in

  Option.iter
    (fun t ->
      Target.run_pre_initial_check_hook t
        (List.filter_map (function File { filename; _ } -> Some filename | Generated _ -> None) parsed_files)
    )
    target;

  let (ctx, vs_ids, regs), processed =
    process_files ~target_name ~default_sail_dir ~options Initial_check.initial_ctx IdSet.empty [] parsed_files
  in
  let processed =
    [ProcessedGenerated (Initial_check.generate_undefineds vs_ids)]
    @ processed
    @ [ProcessedGenerated (Initial_check.generate_initialize_registers vs_ids regs)]
  in

  let t = Profile.start () in
  let env, checked = check_files env processed in
  Profile.finish "type checking" t;

  finalize_ast asserts_termination ctx env (concat_ast checked)

let rewrite_ast_initial effect_info env =
  Rewrites.rewrite Initial_check.initial_ctx effect_info env
    [("initial", fun ctx effect_info env ast -> (ctx, Rewriter.rewrite_ast ast, effect_info, env))]

let initial_rewrite effect_info type_envs ast =
  let _, ast, _, _ = rewrite_ast_initial effect_info type_envs ast in
  (* Recheck after descattering so that the internal type environments
     always have complete variant types *)
  Type_error.check Type_check.initial_env (Type_check.strip_ast ast)
