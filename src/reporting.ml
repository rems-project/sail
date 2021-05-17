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

let opt_warnings = ref true

type pos_or_loc = Loc of Parse_ast.l | Pos of Lexing.position

let print_err_internal p_l m1 m2 =
  let open Error_format in
  prerr_endline (m1 ^ ":");
  begin match p_l with
  | Loc l -> format_message (Location (l, Line m2)) err_formatter
  | Pos p -> format_message (Location (Parse_ast.Range (p, p), Line m2)) err_formatter
  end

let loc_to_string ?code:(code=true) l =
  let open Error_format in
  let b = Buffer.create 160 in
  format_message (Location (l, Line "")) (buffer_formatter b);
  Buffer.contents b

let rec simp_loc = function
  | Parse_ast.Unknown -> None
  | Parse_ast.Unique (_, l) -> simp_loc l
  | Parse_ast.Generated l -> simp_loc l
  | Parse_ast.Range (p1, p2) -> Some (p1, p2)
  | Parse_ast.Documented (_, l) -> simp_loc l

let short_loc_to_string l =
  match simp_loc l with
  | None -> "unknown location"
  | Some (p1, p2) ->
     Printf.sprintf "%s %d:%d - %d:%d"
       p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol)
 
let loc_to_coverage l =
  match simp_loc l with
  | None -> None
  | Some (p1, p2) -> Some (p1.pos_fname, p1.pos_cnum - p1.pos_bol, p2.pos_lnum, p2.pos_cnum - p2.pos_bol)
    
let print_err l m1 m2 =
  print_err_internal (Loc l) m1 m2

type error =
  | Err_general of Parse_ast.l * string
  | Err_unreachable of Parse_ast.l * (string * int * int * int) * Printexc.raw_backtrace * string
  | Err_todo of Parse_ast.l * string
  | Err_syntax of Lexing.position * string
  | Err_syntax_loc of Parse_ast.l * string
  | Err_lex of Lexing.position * string
  | Err_type of Parse_ast.l * string

let issues = "\nPlease report this as an issue on GitHub at https://github.com/rems-project/sail/issues"

let dest_err = function
  | Err_general (l, m) -> ("Error", Loc l, m)
  | Err_unreachable (l, (file, line, _, _), backtrace, m) ->
     (Printf.sprintf "Internal error: Unreachable code (at \"%s\" line %d)" file line, Loc l, m ^ "\n\n" ^ Printexc.raw_backtrace_to_string backtrace ^ issues)
  | Err_todo (l, m) -> ("Todo", Loc l, m)
  | Err_syntax (p, m) -> ("Syntax error", Pos p, m)
  | Err_syntax_loc (l, m) -> ("Syntax error", Loc l, m)
  | Err_lex (p, s) -> ("Lexical error", Pos p, s)
  | Err_type (l, m) -> ("Type error", Loc l, m)

exception Fatal_error of error

(* Abbreviations for the very common cases *)
let err_todo l m = Fatal_error (Err_todo (l, m))
let err_unreachable l ocaml_pos m =
  let backtrace = Printexc.get_callstack 10 in
  Fatal_error (Err_unreachable (l, ocaml_pos, backtrace, m))
let err_general l m = Fatal_error (Err_general (l, m))
let err_typ l m = Fatal_error (Err_type (l, m))
let err_syntax p m = Fatal_error (Err_syntax (p, m))
let err_syntax_loc l m = Fatal_error (Err_syntax_loc (l, m))
let err_lex p m = Fatal_error (Err_lex (p, m))

let unreachable l pos msg =
  raise (err_unreachable l pos msg)

let print_error e =
  let (m1, pos_l, m2) = dest_err e in
  print_err_internal pos_l m1 m2

(* Warnings *)

module StringSet = Set.Make(String)

let ignored_files = ref StringSet.empty

let suppress_warnings_for_file f =
  ignored_files := StringSet.add f !ignored_files
 
let warn str1 l str2 =
  if !opt_warnings then
    match simp_loc l with
    | None ->
       prerr_endline (Util.("Warning" |> yellow |> clear) ^ ": " ^ str1 ^ "\n" ^ str2 ^ "\n")
    | Some (p1, p2) when not (StringSet.mem p1.pos_fname !ignored_files) ->
       prerr_endline (Util.("Warning" |> yellow |> clear) ^ ": "
                      ^ str1 ^ (if str1 <> "" then " " else "") ^ loc_to_string l ^ str2 ^ "\n")
    | Some _ -> ()
  else
    ()

let simple_warn str = warn str Parse_ast.Unknown ""
