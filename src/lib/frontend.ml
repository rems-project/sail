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
let opt_reformat : string option ref = ref None

let check_ast (asserts_termination : bool) (env : Type_check.Env.t) (ast : uannot ast) :
    Type_check.tannot ast * Type_check.Env.t * Effects.side_effect_info =
  let ast, env = Type_error.check env ast in
  let ast = Scattered.descatter ast in
  let side_effects = Effects.infer_side_effects asserts_termination ast in
  Effects.check_side_effects side_effects ast;
  let () = if !opt_ddump_tc_ast then Pretty_print_sail.pp_ast stdout (Type_check.strip_ast ast) else () in
  (ast, env, side_effects)

let load_files ?target default_sail_dir options type_envs files =
  let t = Profile.start () in

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

  let () = if !opt_ddump_initial_ast then Pretty_print_sail.pp_ast stdout ast else () in

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
  Profile.finish "parsing" t;

  let t = Profile.start () in
  let asserts_termination = Option.fold ~none:false ~some:Target.asserts_termination target in
  let ast, type_envs, side_effects = check_ast asserts_termination type_envs ast in
  Profile.finish "type checking" t;

  (ast, type_envs, side_effects)

let rewrite_ast_initial effect_info env =
  Rewrites.rewrite effect_info env
    [("initial", fun effect_info env ast -> (Rewriter.rewrite_ast ast, effect_info, env))]

let initial_rewrite effect_info type_envs ast =
  let ast, _, _ = rewrite_ast_initial effect_info type_envs ast in
  (* Recheck after descattering so that the internal type environments
     always have complete variant types *)
  Type_error.check Type_check.initial_env (Type_check.strip_ast ast)
