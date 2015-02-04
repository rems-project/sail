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
  | Lem_out

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
		                                     | (Ast.Ord_aux(Ast.Ord_dec,_)) -> Type_internal.Odec)};} in
  Type_check.check (Type_check.Env (d_env, Type_internal.initial_typ_env,Type_internal.nob)) defs 

let open_output_with_check file_name =
  let (temp_file_name, o) = Filename.open_temp_file "ll_temp" "" in
  let o' = Format.formatter_of_out_channel o in
  (o', (o, temp_file_name, file_name))

let always_replace_files = ref true

let close_output_with_check (o, temp_file_name, file_name) =
  let _ = close_out o in
  let do_replace = !always_replace_files || (not (Util.same_content_files temp_file_name file_name)) in
  let _ = if (not do_replace) then Sys.remove temp_file_name
          else Util.move_file temp_file_name file_name in
  ()

let generated_line f =
  Printf.sprintf "Generated by Sail from %s." f

(*let tex_preamble =
  "\\documentclass{article}\n" ^
  "\\usepackage{amsmath,amssymb}\n" ^
  "\\usepackage{color}\n" ^
  "\\usepackage{geometry}\n" ^
  "\\usepackage{alltt}\n" ^
  "\\usepackage{lem}\n" ^
  "\\geometry{a4paper,dvips,twoside,left=22.5mm,right=22.5mm,top=20mm,bottom=30mm}\n" ^
  "\\begin{document}\n"^
  "\\tableofcontents\n\\newpage\n"

let tex_postamble =
  "\\end{document}\n"

(* TODO: make this not cppmem-specific *)
let html_preamble =
"\n" ^
"<?xml version=\"1.0\" encoding=\"utf-8\"?>\n" ^
"<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.1//EN\"\n" ^
"          \"http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd\">\n" ^
"<html xmlns=\"http://www.w3.org/1999/xhtml\">\n" ^
"  <head>\n" ^
"    <meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\"/> \n" ^
"    <title>C/C++ memory model definitions</title>\n" ^
"    <link rel=\"stylesheet\" type=\"text/css\" title=\"cppmem style\" media=\"screen\" href=\"cppmem.css\"/>\n" ^
"  </head>\n" ^
"  <body>\n" ^
"    <h1 id=\"title\">C/C++ memory model definitions</h1>\n" ^
"<pre>\n"

let html_postamble =
"\n" ^
"</pre>\n" ^
"  </body>\n" ^
"</html>\n"
*)

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
      | Lem_out -> assert false
(*      | Some(Typed_ast.Target_html) ->
          begin
            let r = B.html_defs m.typed_ast in
            let (o, ext_o) = open_output_with_check (f' ^ ".html") in
              Printf.fprintf o "<!-- %s -->\n" (generated_line m.filename);
              Printf.fprintf o "%s" html_preamble;
              Printf.fprintf o "%s" (Ulib.Text.to_string r);
              Printf.fprintf o "%s" html_postamble;
              close_output_with_check ext_o
          end
      | Some(Typed_ast.Target_hol) ->
          begin
            let (r_main, r_extra_opt) = B.hol_defs m.typed_ast in
            let hol_header o = begin
              Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
              Printf.fprintf o "open bossLib Theory Parse res_quanTheory\n";
              Printf.fprintf o "open fixedPointTheory finite_mapTheory listTheory pairTheory pred_setTheory\n";
              Printf.fprintf o "open integerTheory set_relationTheory sortingTheory stringTheory wordsTheory\n\n";
              Printf.fprintf o "val _ = numLib.prefer_num();\n\n";
              Printf.fprintf o "\n\n";
              begin
                if m.predecessor_modules <> [] then
                  begin
                    Printf.fprintf o "open";
                    List.iter
                      (fun f -> Printf.fprintf o " %s" f; Printf.fprintf o "Theory")
                      m.predecessor_modules;
                    Printf.fprintf o "\n\n"
                  end
                else
                  ()
              end
            end in
            let _ = begin
              let (o, ext_o) = open_output_with_check (m.module_name ^ "Script.sml") in
              hol_header o;
              Printf.fprintf o "val _ = new_theory \"%s\"\n\n" m.module_name;
              Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
              Printf.fprintf o "val _ = export_theory()\n\n";
              close_output_with_check ext_o;
            end in
            let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o,ext_o) = open_output_with_check (m.module_name ^ "ExtraScript.sml") in
                hol_header o;
                Printf.fprintf o "open %sTheory\n\n" m.module_name;
                Printf.fprintf o "val _ = new_theory \"%sExtra\"\n\n" m.module_name;
                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                Printf.fprintf o "val _ = export_theory()\n\n";
                close_output_with_check ext_o
              end in ()
          end
      | Some(Typed_ast.Target_tex) ->
          begin
            let rr = B.tex_defs m.typed_ast in
            (* complete tex document, wrapped in tex_preamble and tex_postamble *)
            let (^^^^) = Ulib.Text.(^^^) in
            let r' = r"\\section{" ^^^^ Output.tex_escape (Ulib.Text.of_string f') ^^^^ r"}\n" ^^^^ rr in
              alldoc_accum := (!alldoc_accum) @ [r'];
              let (o, ext_o) = open_output_with_check (f' ^ ".tex") in
                Printf.fprintf o "%%%s\n" (generated_line m.filename);
                Printf.fprintf o "%s" tex_preamble;
                Printf.fprintf o "%s" (Ulib.Text.to_string rr);
                Printf.fprintf o "%s" tex_postamble;
                close_output_with_check ext_o;
                (* tex definitions to include in other documents *)
                let header = r"\n%%%% generated from " ^^^^ (Ulib.Text.of_string m.filename) ^^^^ r"\n" in
                let (r,r_usage) = B.tex_inc_defs m.typed_ast in
                let (r,r_usage) = (header ^^^^ r, header ^^^^ r_usage) in
                  alldoc_inc_accum := (!alldoc_inc_accum) @ [r];
                  alldoc_inc_usage_accum := (!alldoc_inc_usage_accum) @ [r_usage];
                  let (o,ext_o) = open_output_with_check (f' ^ "-inc.tex") in
                    Printf.fprintf o "%%%s\n" (generated_line m.filename);
                    Printf.fprintf o "%s" (Ulib.Text.to_string r);
                    close_output_with_check ext_o;
                  let (o, ext_o) = open_output_with_check (f' ^ "-use_inc.tex") in
                    Printf.fprintf o "%%%s\n" (generated_line m.filename);
                    Printf.fprintf o "%s" (Ulib.Text.to_string r_usage);
                    close_output_with_check ext_o
          end
      | Some(Typed_ast.Target_ocaml) ->
          begin
            let (r_main, r_extra_opt) = B.ocaml_defs m.typed_ast in
            let _ = begin
              let (o, ext_o) = open_output_with_check (f' ^ ".ml") in
              Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
              Printf.fprintf o "open Nat_num\n\n";
              Printf.fprintf o "open Sum\n\n";
              Printf.fprintf o "type 'a set = 'a Pset.set\n\n";
              Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
              close_output_with_check ext_o
            end in
            let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o, ext_o) = open_output_with_check (f' ^ "Extra.ml") in
                Printf.fprintf o "(*%s*)\n" (generated_line m.filename);
                Printf.fprintf o "open Nat_num\n";
                Printf.fprintf o "open %s\n\n" m.module_name;
                Printf.fprintf o "type 'a set = 'a Pset.set\n\n";

                Printf.fprintf o "%s" "let run_test n loc b =\n  if b then (Format.printf \"%s : ok\\n\" n) else (Format.printf \"%s : FAILED\\n  %s\\n\\n\" n loc);;\n\n";

                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                close_output_with_check ext_o
             end in ()
          end
      | Some(Typed_ast.Target_isa) ->
          begin
          try begin
            let (r_main, r_extra_opt) = B.isa_defs m.typed_ast in
            let r1 = B.isa_header_defs m.typed_ast in
            let _ =
            begin
                let (o, ext_o) = open_output_with_check (m.module_name ^ ".thy") in
                Printf.fprintf o "header{*%s*}\n\n" (generated_line m.filename);
                Printf.fprintf o "theory \"%s\" \n\n" m.module_name;
                Printf.fprintf o "imports \n \t Main\n";
                Printf.fprintf o "\t \"%s\"\n" isa_thy;
                (*
                Printf.fprintf o "imports \n \t \"%s/num_type\" \n" libpath;
                 *)
                Printf.fprintf o "%s" (Ulib.Text.to_string r1);

                begin
                  if m.predecessor_modules <> [] then
                    begin
                      List.iter (fun f -> Printf.fprintf o "\t \"%s\" \n" f) m.predecessor_modules;
                    end
                  else ()
                end;

                Printf.fprintf o "\nbegin \n\n";
                Printf.fprintf o "%s" (Ulib.Text.to_string r_main);
                Printf.fprintf o "end\n";
                close_output_with_check ext_o
              end in

              let _ = match r_extra_opt with None -> () | Some r_extra ->
              begin
                let (o, ext_o) = open_output_with_check (m.module_name ^ "Extra.thy") in
                Printf.fprintf o "header{*%s*}\n\n" (generated_line m.filename);
                Printf.fprintf o "theory \"%sExtra\" \n\n" m.module_name;
                Printf.fprintf o "imports \n \t Main \"~~/src/HOL/Library/Efficient_Nat\" \"%s\"\n" m.module_name;
                Printf.fprintf o "\nbegin \n\n";
                Printf.fprintf o "%s" (Ulib.Text.to_string r_extra);
                Printf.fprintf o "end\n";
                close_output_with_check ext_o
              end in ()
            end
            with | Trans.Trans_error(l,msg) ->
                    raise (Reporting_basic.Fatal_error (Reporting_basic.Err_trans_header (l, msg)))
          end

      | Some(Typed_ast.Target_coq) ->
          begin
            let r = B.coq_defs m.typed_ast in
            let (o, ext_o) = open_output_with_check (f' ^ ".v") in
              Printf.fprintf o "(* %s *)\n\n" (generated_line m.filename);
              Printf.fprintf o "Require Import Arith.\n";
              Printf.fprintf o "Require Import Bool.\n";
              Printf.fprintf o "Require Import List.\n";
              Printf.fprintf o "Require Import String.\n";
              Printf.fprintf o "Require Import Program.Wf.\n\n";
              Printf.fprintf o "Open Scope nat_scope.\n";
              Printf.fprintf o "Open Scope string_scope.\n\n";
              Printf.fprintf o "%s" (Ulib.Text.to_string r);
              close_output_with_check ext_o
          end*)

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
