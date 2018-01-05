(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

let opt_lem_sequential = ref false
let opt_lem_mwords = ref false

type out_type =
  | Lem_ast_out
  | Lem_out of string option

let get_lexbuf f =
  let in_chan = open_in f in
  let lexbuf = Lexing.from_channel in_chan in
  lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = f;
                                Lexing.pos_lnum = 1;
                                Lexing.pos_bol = 0;
                                Lexing.pos_cnum = 0; };
  lexbuf, in_chan

let parse_file (f : string) : Parse_ast.defs =
  let lexbuf, in_chan = get_lexbuf f in
    try
      let ast = Parser2.file Lexer2.token lexbuf in
      close_in in_chan; ast
    with
    | Parser2.Error ->
       let pos = Lexing.lexeme_start_p lexbuf in
       raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "no information")))
    | Lexer2.LexError(s,p) ->
       raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, s)))

let convert_ast (order : Ast.order) (defs : Parse_ast.defs) : unit Ast.defs = Initial_check.process_ast order defs

let load_file_no_check order f = convert_ast order (parse_file f)

let load_file order env f =
  let ast = convert_ast order (parse_file f) in
  Type_check.check env ast

let opt_just_check = ref false
let opt_ddump_tc_ast = ref false
let opt_ddump_rewrite_ast = ref None
let opt_dno_cast = ref false

let check_ast (defs : unit Ast.defs) : Type_check.tannot Ast.defs * Type_check.Env.t =
  let ienv = if !opt_dno_cast then Type_check.Env.no_casts Type_check.initial_env else Type_check.initial_env in
  let ast, env = Type_check.check ienv defs in
  let () = if !opt_ddump_tc_ast then Pretty_print_sail2.pp_defs stdout ast else () in
  let () = if !opt_just_check then exit 0 else () in
  (ast, env)

let opt_ddump_raw_mono_ast = ref false
let opt_dmono_analysis = ref 0
let opt_auto_mono = ref false

let monomorphise_ast locs type_env ast =
  let ast = Monomorphise.monomorphise (!opt_lem_mwords) (!opt_auto_mono) (!opt_dmono_analysis)
    locs type_env ast in
  let () = if !opt_ddump_raw_mono_ast then Pretty_print_sail2.pp_defs stdout ast else () in
  let ienv = Type_check.Env.no_casts Type_check.initial_env in
  Type_check.check ienv ast

let open_output_with_check file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  (o', (o, temp_file_name, file_name))

let open_output_with_check_unformatted file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  (o, temp_file_name, file_name)

let always_replace_files = ref true

let close_output_with_check (o, temp_file_name, file_name) =
  let _ = close_out o in
  let do_replace = !always_replace_files || (not (Util.same_content_files temp_file_name file_name)) in
  let _ = if (not do_replace) then Sys.remove temp_file_name
          else Util.move_file temp_file_name file_name in
  ()

let generated_line f =
  Printf.sprintf "Generated by Sail from %s." f

let output_lem filename libs defs =
  let generated_line = generated_line filename in
  let seq_suffix = if !opt_lem_sequential then "_sequential" else "" in
  let types_module = (filename ^ "_embed_types" ^ seq_suffix) in
  let monad_module = if !opt_lem_sequential then "State" else "Prompt" in
  let operators_module = if !opt_lem_mwords then "Sail_operators_mwords" else "Sail_operators" in
  let libs = List.map (fun lib -> lib ^ seq_suffix) libs in
  let base_imports = [
      "Pervasives_extra";
      "Sail_impl_base";
      "Sail_values";
      operators_module;
      monad_module
    ] in
  let ((ot,_, _) as ext_ot) =
    open_output_with_check_unformatted (filename ^ "_embed_types" ^ seq_suffix ^ ".lem") in
  let ((o,_, _) as ext_o) =
    open_output_with_check_unformatted (filename ^ "_embed" ^ seq_suffix ^ ".lem") in
  (Pretty_print.pp_defs_lem !opt_lem_sequential !opt_lem_mwords
     (ot, base_imports)
     (o, base_imports @ (String.capitalize types_module :: libs))
     defs generated_line);
  close_output_with_check ext_ot;
  close_output_with_check ext_o

let rec iterate (f : int -> unit) (n : int) : unit =
  if n = 0 then ()
  else (f n; iterate f (n - 1))

let output1 libpath out_arg filename defs  =
  let f' = Filename.basename (Filename.chop_extension filename) in
    match out_arg with
      | Lem_ast_out ->
	begin
	  let (o, ext_o) = open_output_with_check (f' ^ ".lem") in
	  Format.fprintf o "(* %s *)@\n" (generated_line filename);
          Format.fprintf o "open import Interp_ast@\n";
	  Format.fprintf o "open import Pervasives@\n";
          Format.fprintf o "(*Supply common numeric constants at the right type to alleviate repeated calls to typeclass macro*)\n";
          iterate (fun n -> Format.fprintf o "let int%i : integer = integerFromNat %i\n" (n - 1) (n - 1)) 129;
          Format.fprintf o "let defs = ";
	  Pretty_print.pp_lem_defs o defs;
	  close_output_with_check ext_o
	end
      | Lem_out None ->
        output_lem f' [] defs
      | Lem_out (Some lib) ->
        output_lem f' [lib] defs

let output libpath out_arg files =
  List.iter
    (fun (f, defs) ->
       output1 libpath out_arg f defs)
    files

let rewrite_step defs (name,rewriter) =
  let defs = rewriter defs in
  let _ = match !(opt_ddump_rewrite_ast) with
    | Some (f, i) ->
      begin
        let filename = f ^ "_rewrite_" ^ string_of_int i ^ "_" ^ name ^ ".sail" in
        (* output "" Lem_ast_out [filename, defs]; *)
        let ((ot,_, _) as ext_ot) = open_output_with_check_unformatted filename in
        Pretty_print_sail2.pp_defs ot defs;
        close_output_with_check ext_ot;
        opt_ddump_rewrite_ast := Some (f, i + 1)
      end
    | _ -> () in
  defs

let rewrite rewriters defs =
  try List.fold_left rewrite_step defs rewriters with
  | Type_check.Type_error (l, err) ->
     raise (Reporting_basic.err_typ l (Type_check.string_of_type_error err))

let rewrite_ast = rewrite [("initial", Rewriter.rewrite_defs)]
let rewrite_undefined = rewrite [("undefined", fun x -> Rewrites.rewrite_undefined !opt_lem_mwords x)]
let rewrite_ast_lem = rewrite Rewrites.rewrite_defs_lem
let rewrite_ast_ocaml = rewrite Rewrites.rewrite_defs_ocaml
let rewrite_ast_interpreter = rewrite Rewrites.rewrite_defs_interpreter
let rewrite_ast_sil = rewrite Rewrites.rewrite_defs_sil
let rewrite_ast_check = rewrite Rewrites.rewrite_defs_check
