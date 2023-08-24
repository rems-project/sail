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

(* Currently limited to:
   - functions, no scattered, no preprocessor
   - no new undefined functions (but no explicit check here yet)
*)

open Ast
open Ast_defs
open Ast_util

let scan_ast { defs; _ } =
  let scan (ids, specs) (DEF_aux (aux, _) as def) =
    match aux with
    | DEF_fundef fd -> (IdSet.add (id_of_fundef fd) ids, specs)
    | DEF_val (VS_aux (VS_val_spec (_, id, _), _) as vs) -> (ids, Bindings.add id vs specs)
    | DEF_pragma (("file_start" | "file_end"), _, _) -> (ids, specs)
    | _ -> raise (Reporting.err_general (def_loc def) "Definition in splice file isn't a spec or function")
  in
  List.fold_left scan (IdSet.empty, Bindings.empty) defs

let filter_old_ast repl_ids repl_specs { defs; _ } =
  let check (rdefs, spec_found) (DEF_aux (aux, def_annot) as def) =
    match aux with
    | DEF_fundef fd ->
        let id = id_of_fundef fd in
        if IdSet.mem id repl_ids then (rdefs, spec_found) else (def :: rdefs, spec_found)
    | DEF_val (VS_aux (VS_val_spec (_, id, _), _)) -> (
        match Bindings.find_opt id repl_specs with
        | Some vs -> (DEF_aux (DEF_val vs, def_annot) :: rdefs, IdSet.add id spec_found)
        | None -> (def :: rdefs, spec_found)
      )
    | _ -> (def :: rdefs, spec_found)
  in
  let rdefs, spec_found = List.fold_left check ([], IdSet.empty) defs in
  (List.rev rdefs, spec_found)

let filter_replacements spec_found { defs; _ } =
  let not_found = function
    | DEF_aux (DEF_val (VS_aux (VS_val_spec (_, id, _), _)), _) -> not (IdSet.mem id spec_found)
    | _ -> true
  in
  List.filter not_found defs

let splice ast file =
  let parsed_ast = Initial_check.parse_file file |> snd in
  let repl_ast = Initial_check.process_ast ~generate:false (Parse_ast.Defs [(file, parsed_ast)]) in
  let repl_ast = Rewrites.move_loop_measures repl_ast in
  let repl_ast = map_ast_annot (fun (l, _) -> (l, Type_check.empty_tannot)) repl_ast in
  let repl_ids, repl_specs = scan_ast repl_ast in
  let defs1, specs_found = filter_old_ast repl_ids repl_specs ast in
  let defs2 = filter_replacements specs_found repl_ast in
  Type_error.check Type_check.initial_env (Type_check.strip_ast { ast with defs = defs1 @ defs2 })
