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

let rec skip_lines in_chan = function
  | n when n <= 0 -> ()
  | n -> ignore (input_line in_chan); skip_lines in_chan (n - 1)

let rec read_lines in_chan = function
  | n when n <= 0 -> []
  | n ->
     let l = input_line in_chan in
     let ls = read_lines in_chan (n - 1) in
     l :: ls

let termcode n = "\x1B[" ^ string_of_int n ^ "m"

let print_code1 ff fname lnum1 cnum1 cnum2 =
  try
    let in_chan = open_in fname in
    begin
      try
        skip_lines in_chan (lnum1 - 1);
        let line = input_line in_chan in
        Format.fprintf ff "%s%s%s%s%s"
                       (Str.string_before line cnum1)
                       (termcode 41)
                       (Str.string_before (Str.string_after line cnum1) (cnum2 - cnum1))
                       (termcode 49)
                       (Str.string_after line cnum2);
        close_in in_chan
      with e -> (close_in_noerr in_chan; print_endline (Printexc.to_string e))
    end
  with _ -> ()

let format_pos ff p =
  let open Lexing in
  begin
    Format.fprintf ff "file \"%s\", line %d, character %d:\n\n"
                   p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol);
    print_code1 ff p.pos_fname p.pos_lnum (p.pos_cnum - p.pos_bol) (p.pos_cnum - p.pos_bol + 1);
    Format.fprintf ff "\n\n";
    Format.pp_print_flush ff ()
  end

let print_code2 ff fname lnum1 cnum1 lnum2 cnum2 =
  try
    let in_chan = open_in fname in
    begin
      try
        skip_lines in_chan (lnum1 - 1);
        let line = input_line in_chan in
        Format.fprintf ff "%s%s%s%s\n"
                       (Str.string_before line cnum1)
                       (termcode 41)
                       (Str.string_after line cnum1)
                       (termcode 49);
        let lines = read_lines in_chan (lnum2 - lnum1 - 1) in
        List.iter (fun l -> Format.fprintf ff "%s%s%s\n" (termcode 41) l (termcode 49)) lines;
        let line = input_line in_chan in
        Format.fprintf ff "%s%s%s%s"
                       (termcode 41)
                       (Str.string_before line cnum2)
                       (termcode 49)
                       (Str.string_after line cnum2);
        close_in in_chan
      with e -> (close_in_noerr in_chan; print_endline (Printexc.to_string e))
    end
  with _ -> ()

let format_pos2 ff p1 p2 =
  let open Lexing in
  begin
    Format.fprintf ff "file \"%s\", line %d, character %d to line %d, character %d\n\n"
                   p1.pos_fname
                   p1.pos_lnum (p1.pos_cnum - p1.pos_bol + 1)
                   p2.pos_lnum (p2.pos_cnum - p2.pos_bol);
    if p1.pos_lnum == p2.pos_lnum
    then print_code1 ff p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) (p2.pos_cnum - p2.pos_bol)
    else print_code2 ff p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum (p2.pos_cnum - p2.pos_bol);
    Format.pp_print_flush ff ()
  end

(* reads the part between p1 and p2 from the file *)

let read_from_file_pos2 p1 p2 =
  let (s, e, multi) = if p1.Lexing.pos_lnum = p2.Lexing.pos_lnum then
                  (* everything in the same line, so really only read this small part*)
                  (p1.Lexing.pos_cnum, p2.Lexing.pos_cnum, None) 
               else (*multiline, so start reading at beginning of line *)
                  (p1.Lexing.pos_bol, p2.Lexing.pos_cnum, Some (p1.Lexing.pos_cnum - p1.Lexing.pos_bol)) in

  let ic = open_in p1.Lexing.pos_fname in
  let _ = seek_in ic s in
  let l = (e - s) in
  let buf = Bytes.create l in
  let _ = input ic buf 0 l in
  let _ = match multi with None -> () | Some sk -> Bytes.fill buf 0 sk ' ' in
  let _ = close_in ic in
  (buf, not (multi = None))

(* Destruct a location by splitting all the Internal strings except possibly the
   last one into a string list and keeping only the last location *)
let dest_loc (l : Parse_ast.l) : (Parse_ast.l * string list) = 
  let rec aux acc l = match l with
    | Parse_ast.Int(s, Some l') -> aux (s::acc) l'
    | _ -> (l, acc)
  in
  aux [] l

let rec format_loc_aux ff l =
  let (l_org, mod_s) = dest_loc l in
  let _ = match l_org with
    | Parse_ast.Unknown -> Format.fprintf ff "no location information available"
    | Parse_ast.Generated l -> Format.fprintf ff "Code generated: original nearby source is "; (format_loc_aux ff l)
    | Parse_ast.Range(p1,p2) -> format_pos2 ff p1 p2
    | Parse_ast.Int(s,_) -> Format.fprintf ff "code in lib from: %s" s
  in
  ()

let format_loc_source ff l = 
  match dest_loc l with 
  | (Parse_ast.Range (p1, p2), _) -> 
    begin
      let (s, multi_line) = read_from_file_pos2 p1 p2 in
      if multi_line then 
        Format.fprintf ff "  original input:\n%s\n" (Bytes.to_string s)
      else
        Format.fprintf ff "  original input: \"%s\"\n" (Bytes.to_string s)
    end
  | _ -> ()

let format_loc ff l =
 (format_loc_aux ff l;
  Format.pp_print_newline ff ();
  Format.pp_print_flush ff ()
);;

let print_err_loc l = 
   (format_loc Format.err_formatter l)

let print_pos p = format_pos Format.std_formatter p
let print_err_pos p = format_pos Format.err_formatter p

let loc_to_string l =
  let _ = Format.flush_str_formatter () in
  let _ = format_loc_aux Format.str_formatter l in
  let s = Format.flush_str_formatter () in
  s

type pos_or_loc = Loc of Parse_ast.l | LocD of Parse_ast.l * Parse_ast.l | Pos of Lexing.position

let print_err_internal fatal verb_loc p_l m1 m2 =
  Format.eprintf "%s at " m1;
  let _ = (match p_l with Pos p -> print_err_pos p
                        | Loc l -> print_err_loc l
                        | LocD (l1,l2) ->
                          print_err_loc l1; Format.fprintf Format.err_formatter " and "; print_err_loc l2) in
  Format.eprintf "%s\n" m2;
  if verb_loc then (match p_l with Loc l ->
      format_loc_source Format.err_formatter l;
      Format.pp_print_newline Format.err_formatter (); | _ -> ());
  Format.pp_print_flush Format.err_formatter ();
  if fatal then (exit 1) else ()

let print_err fatal verb_loc l m1 m2 =
  print_err_internal fatal verb_loc (Loc l) m1 m2

type error =
  | Err_general of Parse_ast.l * string
  | Err_unreachable of Parse_ast.l * string
  | Err_todo of Parse_ast.l * string
  | Err_syntax of Lexing.position * string
  | Err_syntax_locn of Parse_ast.l * string
  | Err_lex of Lexing.position * string
  | Err_type of Parse_ast.l * string
  | Err_type_dual of Parse_ast.l * Parse_ast.l * string

let dest_err = function
  | Err_general (l, m) -> ("Error", false, Loc l, m)
  | Err_unreachable (l, m) -> ("Internal error: Unreachable code", false, Loc l, m)
  | Err_todo (l, m) -> ("Todo" ^ m, false, Loc l, "")
  | Err_syntax (p, m) -> ("Syntax error", false, Pos p, m)
  | Err_syntax_locn (l, m) -> ("Syntax error", false, Loc l, m)
  | Err_lex (p, s) -> ("Lexical error", false, Pos p, s)
  | Err_type (l, m) -> ("Type error", false, Loc l, m)
  | Err_type_dual(l1,l2,m) -> ("Type error", false, LocD (l1,l2), m)

exception Fatal_error of error

(* Abbreviations for the very common cases *)
let err_todo l m = Fatal_error (Err_todo (l, m))
let err_unreachable l m = Fatal_error (Err_unreachable (l, m))
let err_general l m = Fatal_error (Err_general (l, m))
let err_typ l m = Fatal_error (Err_type (l,m))
let err_typ_dual l1 l2 m = Fatal_error (Err_type_dual (l1,l2,m))

let report_error e = 
  let (m1, verb_pos, pos_l, m2) = dest_err e in
  (print_err_internal verb_pos false pos_l m1 m2; exit 1)

let print_error e =
  let (m1, verb_pos, pos_l, m2) = dest_err e in
  print_err_internal verb_pos false pos_l m1 m2
