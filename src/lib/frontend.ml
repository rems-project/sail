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

open Ast_util
open Ast_defs

module StringMap = Map.Make (String)

let opt_ddump_initial_ast = ref false
let opt_ddump_tc_ast = ref false
let opt_list_files = ref false
let opt_reformat : string option ref = ref None

let check_ast (asserts_termination : bool) (env : Type_check.Env.t) (ast : uannot ast) :
    Type_check.tannot ast * Type_check.Env.t * Effects.side_effect_info =
  let ast, env = Type_error.check env ast in
  let ast = Scattered.descatter ast in
  let side_effects = Effects.infer_side_effects asserts_termination ast in
  Effects.check_side_effects side_effects ast;
  let () = if !opt_ddump_tc_ast then Pretty_print_sail.pp_ast stdout (Type_check.strip_ast ast) else () in
  (ast, env, side_effects)

let instantiate_abstract_types insts ast =
  let open Ast in
  let instantiate = function
    | DEF_aux (DEF_type (TD_aux (TD_abstract (id, kind), (l, _))), def_annot) as def -> begin
        match Bindings.find_opt id insts with
        | Some arg ->
            let arg_kind = typ_arg_kind arg in
            if Kind.compare arg_kind kind <> 0 then
              raise
                (Reporting.err_general l
                   (Printf.sprintf
                      "Failed to instantiate abstract type. Abstract type has kind %s, but instantiation has kind %s"
                      (string_of_kind kind) (string_of_kind arg_kind)
                   )
                );
            DEF_aux
              ( DEF_type (TD_aux (TD_abbrev (id, mk_empty_typquant ~loc:(gen_loc l), arg), (l, Type_check.empty_tannot))),
                def_annot
              )
        | None -> def
      end
    | def -> def
  in
  { ast with defs = List.map instantiate ast.defs }

type parsed_module = {
  id : Project.mod_id;
  included : bool;
  files : (string * (Lexer.comment list * Parse_ast.def list)) list;
}

let wrap_module proj parsed_module =
  let module P = Parse_ast in
  let open Project in
  let name, l = module_name proj parsed_module.id in
  let bracket_pragma p = P.DEF_aux (P.DEF_pragma (p, name, 1), to_loc l) in
  parsed_module.files
  |> Util.update_first (fun (f, (comments, defs)) -> (f, (comments, bracket_pragma "start_module#" :: defs)))
  |> Util.update_last (fun (f, (comments, defs)) -> (f, (comments, defs @ [bracket_pragma "end_module#"])))

let process_ast target type_envs ast =
  if !opt_ddump_initial_ast then Pretty_print_sail.pp_ast stdout ast;

  begin
    match !opt_reformat with
    | Some dir ->
        Pretty_print_sail.reformat dir ast;
        exit 0
    | None -> ()
  end;

  (* The separate loop measures declarations would be awkward to type check, so
     move them into the definitions beforehand. *)
  let ast = Rewrites.move_loop_measures ast in

  let t = Profile.start () in
  let asserts_termination = Option.fold ~none:false ~some:Target.asserts_termination target in
  let ast, type_envs, side_effects = check_ast asserts_termination type_envs ast in
  Profile.finish "type checking" t;

  (ast, type_envs, side_effects)

let load_modules ?target default_sail_dir options type_envs proj root_mod_ids =
  let open Project in
  let mod_ids = module_order proj in
  let is_included = required_modules proj ~roots:(ModSet.of_list root_mod_ids) in

  let parsed_modules =
    List.map
      (fun mod_id ->
        let files = module_files proj mod_id in
        {
          id = mod_id;
          included = is_included mod_id;
          files = List.map (fun f -> (fst f, Initial_check.parse_file (fst f))) files;
        }
      )
      mod_ids
  in

  if !opt_list_files then (
    let included_files =
      List.map (fun parsed_module -> if parsed_module.included then parsed_module.files else []) parsed_modules
      |> List.concat
    in
    print_endline (Util.string_of_list " " fst included_files);
    exit 0
  );

  let comments =
    List.map (fun m -> List.map (fun (f, (comments, _)) -> (f, comments)) m.files) parsed_modules |> List.concat
  in
  let target_name = Option.map Target.name target in

  let ast =
    let files = List.concat (List.map (wrap_module proj) parsed_modules) in
    let files =
      List.map
        (fun (f, (_, file_ast)) -> (f, Preprocess.preprocess default_sail_dir target_name options file_ast))
        files
    in
    Parse_ast.Defs files
  in
  let ast = Initial_check.process_ast ~generate:true ast in
  let ast = { ast with comments } in
  process_ast target type_envs ast

let load_files ?target default_sail_dir options type_envs files =
  let parsed_files = List.map (fun f -> (f, Initial_check.parse_file f)) files in

  let comments = List.map (fun (f, (comments, _)) -> (f, comments)) parsed_files in
  let target_name = Option.map Target.name target in
  let ast =
    Parse_ast.Defs
      (List.map
         (fun (f, (_, file_ast)) -> (f, Preprocess.preprocess default_sail_dir target_name options file_ast))
         parsed_files
      )
  in
  let ast = Initial_check.process_ast ~generate:true ast in
  let ast = { ast with comments } in
  process_ast target type_envs ast

let rewrite_ast_initial effect_info env =
  Rewrites.rewrite effect_info env
    [("initial", fun effect_info env ast -> (Rewriter.rewrite_ast ast, effect_info, env))]

let initial_rewrite effect_info type_envs ast =
  let ast, _, _ = rewrite_ast_initial effect_info type_envs ast in
  (* Recheck after descattering so that the internal type environments
     always have complete variant types *)
  Type_error.check Type_check.initial_env (Type_check.strip_ast ast)
