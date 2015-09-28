(**************************************************************************)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2013                               *)
(*  by the UK authors above and Institut National de Recherche en         *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(**************************************************************************)

open Type_internal

type out_type =
  | Lem_ast_out
  | Ocaml_out of string option

(* let r = Ulib.Text.of_latin1 *)

let get_lexbuf fn =
  let lexbuf = Lexing.from_channel (open_in fn) in
    lexbuf.Lexing.lex_curr_p <- { Lexing.pos_fname = fn;
                                  Lexing.pos_lnum = 1;
                                  Lexing.pos_bol = 0;
                                  Lexing.pos_cnum = 0; };
    lexbuf

let parse_file (f : string) : Parse_ast.defs =
  let scanbuf = get_lexbuf f in
  let type_names = 
    try
      Pre_parser.file Pre_lexer.token scanbuf
    with
      | Parsing.Parse_error ->
          let pos = Lexing.lexeme_start_p scanbuf in
           raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "pre")))
      | Parse_ast.Parse_error_locn(l,m) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, m)))
      | Lexer.LexError(s,p) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, s))) in
  let () = Lexer.custom_type_names := !Lexer.custom_type_names @ type_names in
  let lexbuf = get_lexbuf f in
    try
      Parser.file Lexer.token lexbuf
    with
      | Parsing.Parse_error ->
          let pos = Lexing.lexeme_start_p lexbuf in
           raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos, "main")))
      | Parse_ast.Parse_error_locn(l,m) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax_locn (l, m)))
      | Lexer.LexError(s,p) ->
          raise (Reporting_basic.Fatal_error (Reporting_basic.Err_lex (p, s)))

(*Should add a flag to say whether we want to consider Oinc or Odec the default order *)
let convert_ast (defs : Parse_ast.defs) : (Type_internal.tannot Ast.defs * kind Envmap.t * Ast.order)=
  Initial_check.to_ast Nameset.empty Type_internal.initial_kind_env (Ast.Ord_aux(Ast.Ord_inc,Parse_ast.Unknown)) defs


let check_ast (defs : Type_internal.tannot Ast.defs) (k : kind Envmap.t) (o:Ast.order) : Type_internal.tannot Ast.defs =
  let d_env = { Type_internal.k_env = k; Type_internal.abbrevs = Type_internal.initial_abbrev_env; 
		Type_internal.namesch = Envmap.empty; Type_internal.enum_env = Envmap.empty; 
		Type_internal.rec_env = []; Type_internal.alias_env = Envmap.empty; 
		Type_internal.default_o = 
                {Type_internal.order = (match o with | (Ast.Ord_aux(Ast.Ord_inc,_)) -> Type_internal.Oinc 
		                                     | (Ast.Ord_aux(Ast.Ord_dec,_)) -> Type_internal.Odec
						     | _ -> Type_internal.Oinc)};} in
  Type_check.check (Type_check.Env (d_env, Type_internal.initial_typ_env,Type_internal.nob,Envmap.empty)) defs 

let rewrite_ast (defs: Type_internal.tannot Ast.defs) = Rewriter.rewrite_defs defs

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

let output1 libpath out_arg filename defs (* alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum*) =
  let f' = Filename.basename (Filename.chop_extension filename) in
    match out_arg with
      | Lem_ast_out ->
	begin
	  let (o, ext_o) = open_output_with_check (f' ^ ".lem") in
	  Format.fprintf o "(* %s *)@\n" (generated_line filename);
          Format.fprintf o "open import Interp_ast@\n";
	  Format.fprintf o "open import Pervasives@\n";
          Format.fprintf o "(*Supply common numeric constants at the right type to alleviate repeated calls to typeclass macro*)\n";
          Format.fprintf o "let zero  : integer = integerFromNat 0\n";
          Format.fprintf o "let one   : integer = integerFromNat 1\n";
          Format.fprintf o "let two   : integer = integerFromNat 2\n";
          Format.fprintf o "let three : integer = integerFromNat 3\n";
          Format.fprintf o "let four  : integer = integerFromNat 4\n";
          Format.fprintf o "let five  : integer = integerFromNat 5\n";
          Format.fprintf o "let six   : integer = integerFromNat 6\n";
          Format.fprintf o "let seven : integer = integerFromNat 7\n";
          Format.fprintf o "let eight : integer = integerFromNat 8\n";
          Format.fprintf o "let fifteen : integer = integerFromNat 15\n";
          Format.fprintf o "let sixteen : integer = integerFromNat 16\n";
          Format.fprintf o "let twenty  : integer = integerFromNat 20\n";
          Format.fprintf o "let twentythree : integer = integerFromNat 23\n";
          Format.fprintf o "let twentyfour  : integer = integerFromNat 24\n";
          Format.fprintf o "let thirty : integer = integerFromNat 30\n";
          Format.fprintf o "let thirtyone  : integer = integerFromNat 31\n";
          Format.fprintf o "let thirtytwo  : integer = integerFromNat 32\n";
          Format.fprintf o "let thirtyfive : integer = integerFromNat 35\n";
          Format.fprintf o "let thirtynine : integer = integerFromNat 39\n";
          Format.fprintf o "let forty : integer = integerFromNat 40\n";
          Format.fprintf o "let fortyseven : integer = integerFromNat 47\n";
          Format.fprintf o "let fortyeight : integer = integerFromNat 48\n";
          Format.fprintf o "let fiftyfive  : integer = integerFromNat 55\n";
          Format.fprintf o "let fiftysix   : integer = integerFromNat 56\n";
          Format.fprintf o "let fiftyseven : integer = integerFromNat 57\n";
          Format.fprintf o "let sixtyone   : integer = integerFromNat 61\n";
          Format.fprintf o "let sixtythree : integer = integerFromNat 63\n";
          Format.fprintf o "let sixtyfour  : integer = integerFromNat 64\n";
          Format.fprintf o "let onetwentyseven : integer = integerFromNat 127\n";
          Format.fprintf o "let onetwentyeight : integer = integerFromNat 128\n";
                    
          Format.fprintf o "let defs = ";
	  Pretty_print.pp_lem_defs o defs;
	  close_output_with_check ext_o
	end
      | Ocaml_out None ->
        let ((o,temp_file_name, filename) as ext_o) = open_output_with_check_unformatted (f' ^ ".ml") in
	begin Pretty_print.pp_defs_ocaml o defs (generated_line filename) ["sail_values"];
        close_output_with_check ext_o
        end
      | Ocaml_out (Some lib) ->
        let ((o,temp_file_name, filename) as ext_o) = open_output_with_check_unformatted (f' ^ ".ml") in
	Pretty_print.pp_defs_ocaml o defs (generated_line filename) ["sail_values"; lib];
        close_output_with_check ext_o


let output libpath out_arg files (*alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum*) =
  List.iter
    (fun (f, defs) ->
       output1 libpath out_arg f defs (*alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum*))
    files


(*let output_alldoc f' fs alldoc_accum alldoc_inc_accum alldoc_inc_usage_accum =
  let rs = !alldoc_accum in
  let (o, ext_o) = open_output_with_check (f' ^ ".tex") in
  Printf.fprintf o "%%%s\n" (generated_line fs);
  Printf.fprintf o "%s" tex_preamble;
  Printf.fprintf o "%s" (Ulib.Text.to_string (Ulib.Text.concat (r"") rs));
  Printf.fprintf o "%s" tex_postamble;
  close_output_with_check ext_o;
  let rs = !alldoc_inc_accum in
  let (o, ext_o) = open_output_with_check (f' ^ "-inc.tex") in
  Printf.fprintf o "%%%s\n" (generated_line fs);
  Printf.fprintf o "%s" (Ulib.Text.to_string (Ulib.Text.concat (r"") rs));
  close_output_with_check ext_o;
  let rs = !alldoc_inc_usage_accum in
  let (o, ext_o) = open_output_with_check (f' ^ "-use_inc.tex") in
  Printf.fprintf o "%%%s\n" (generated_line fs);
  Printf.fprintf o "%s" (Ulib.Text.to_string (Ulib.Text.concat (r"") rs));
  close_output_with_check ext_o

*)
