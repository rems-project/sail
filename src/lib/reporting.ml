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
let opt_backtrace_length = ref 10

type pos_or_loc = Loc of Parse_ast.l | Pos of Lexing.position

let fix_endline str = if str.[String.length str - 1] = '\n' then String.sub str 0 (String.length str - 1) else str

let print_err_internal p_l m1 m2 =
  let open Error_format in
  prerr_endline (m1 ^ ":");
  begin
    match p_l with
    | Loc l -> format_message (Location ("", None, l, Line (fix_endline m2))) err_formatter
    | Pos p -> format_message (Location ("", None, Parse_ast.Range (p, p), Line (fix_endline m2))) err_formatter
  end

let loc_to_string l =
  let open Error_format in
  let b = Buffer.create 160 in
  format_message (Location ("", None, l, Line "")) (buffer_formatter b);
  Buffer.contents b

let rec simp_loc = function
  | Parse_ast.Unknown -> None
  | Parse_ast.Unique (_, l) -> simp_loc l
  | Parse_ast.Generated l -> simp_loc l
  | Parse_ast.Hint (_, l1, l2) -> begin match simp_loc l1 with None -> simp_loc l2 | pos -> pos end
  | Parse_ast.Range (p1, p2) -> Some (p1, p2)

let rec loc_file = function
  | Parse_ast.Unknown -> None
  | Parse_ast.Unique (_, l) -> loc_file l
  | Parse_ast.Generated l -> loc_file l
  | Parse_ast.Hint (_, _, l) -> loc_file l
  | Parse_ast.Range (p1, _) -> Some p1.pos_fname

let rec start_loc = function
  | Parse_ast.Unknown -> Parse_ast.Unknown
  | Parse_ast.Unique (u, l) -> Parse_ast.Unique (u, start_loc l)
  | Parse_ast.Generated l -> Parse_ast.Generated (start_loc l)
  | Parse_ast.Hint (hint, l1, l2) -> Parse_ast.Hint (hint, start_loc l1, start_loc l2)
  | Parse_ast.Range (p1, _) -> Parse_ast.Range (p1, p1)

let short_loc_to_string l =
  match simp_loc l with
  | None -> "unknown location"
  | Some (p1, p2) ->
      Printf.sprintf "%s:%d.%d-%d.%d" p1.pos_fname p1.pos_lnum (p1.pos_cnum - p1.pos_bol) p2.pos_lnum
        (p2.pos_cnum - p2.pos_bol)

let print_err l m1 m2 = print_err_internal (Loc l) m1 m2

type error =
  | Err_general of Parse_ast.l * string
  | Err_unreachable of Parse_ast.l * (string * int * int * int) * Printexc.raw_backtrace * string
  | Err_todo of Parse_ast.l * string
  | Err_syntax of Lexing.position * string
  | Err_syntax_loc of Parse_ast.l * string
  | Err_lex of Lexing.position * string
  | Err_type of Parse_ast.l * string option * string

let issues = "\nPlease report this as an issue on GitHub at https://github.com/rems-project/sail/issues"

let dest_err ?(interactive = false) = function
  | Err_general (l, m) -> (Util.("Error" |> yellow |> clear), Loc l, m)
  | Err_unreachable (l, (file, line, _, _), backtrace, m) ->
      if interactive then ("Error", Loc l, m)
      else
        ( Printf.sprintf "Internal error: Unreachable code (at \"%s\" line %d)" file line,
          Loc l,
          m ^ "\n\n" ^ Printexc.raw_backtrace_to_string backtrace ^ issues
        )
  | Err_todo (l, m) -> ("Todo", Loc l, m)
  | Err_syntax (p, m) -> (Util.("Syntax error" |> yellow |> clear), Pos p, m)
  | Err_syntax_loc (l, m) -> (Util.("Syntax error" |> yellow |> clear), Loc l, m)
  | Err_lex (p, s) -> (Util.("Lexical error" |> yellow |> clear), Pos p, s)
  | Err_type (l, _, m) -> (Util.("Type error" |> yellow |> clear), Loc l, m)

exception Fatal_error of error

(* Abbreviations for the very common cases *)
let err_todo l m = Fatal_error (Err_todo (l, m))
let err_unreachable l ocaml_pos m =
  let backtrace = Printexc.get_callstack !opt_backtrace_length in
  Fatal_error (Err_unreachable (l, ocaml_pos, backtrace, m))
let err_general l m = Fatal_error (Err_general (l, m))
let err_typ ?hint l m = Fatal_error (Err_type (l, hint, m))
let err_syntax p m = Fatal_error (Err_syntax (p, m))
let err_syntax_loc l m = Fatal_error (Err_syntax_loc (l, m))
let err_lex p m = Fatal_error (Err_lex (p, m))

let unreachable l pos msg = raise (err_unreachable l pos msg)

let forbid_errors ocaml_pos f x =
  try f x with
  | Fatal_error (Err_general (l, m)) -> raise (err_unreachable l ocaml_pos m)
  | Fatal_error (Err_todo (l, m)) -> raise (err_unreachable l ocaml_pos m)
  | Fatal_error (Err_syntax (p, m)) -> raise (err_unreachable (Range (p, p)) ocaml_pos m)
  | Fatal_error (Err_syntax_loc (l, m)) -> raise (err_unreachable l ocaml_pos m)
  | Fatal_error (Err_lex (p, m)) -> raise (err_unreachable (Range (p, p)) ocaml_pos m)
  | Fatal_error (Err_type (l, _, m)) -> raise (err_unreachable l ocaml_pos m)

let print_error ?(interactive = false) e =
  let m1, pos_l, m2 = dest_err ~interactive e in
  print_err_internal pos_l m1 m2

(* Warnings *)

module StringSet = Set.Make (String)

let pos_compare p1 p2 =
  let open Lexing in
  match String.compare p1.pos_fname p2.pos_fname with
  | 0 -> begin
      match compare p1.pos_lnum p2.pos_lnum with
      | 0 -> begin match compare p1.pos_bol p2.pos_bol with 0 -> compare p1.pos_cnum p2.pos_cnum | n -> n end
      | n -> n
    end
  | n -> n

module Range = struct
  type t = Lexing.position * Lexing.position
  let compare (p1, p2) (p3, p4) =
    let c = pos_compare p1 p3 in
    if c = 0 then pos_compare p2 p4 else c
end

module RangeMap = Map.Make (Range)

let ignored_files = ref StringSet.empty

let suppress_warnings_for_file f = ignored_files := StringSet.add f !ignored_files

let seen_warnings = ref RangeMap.empty
let once_from_warnings = ref StringSet.empty

let warn ?once_from short_str l explanation =
  let already_shown =
    match once_from with
    | Some (file, lnum, cnum, enum) ->
        let key = Printf.sprintf "%d:%d:%d:%s" lnum cnum enum file in
        if StringSet.mem key !once_from_warnings then true
        else (
          once_from_warnings := StringSet.add key !once_from_warnings;
          false
        )
    | None -> false
  in
  if !opt_warnings && not already_shown then (
    match simp_loc l with
    | Some (p1, p2) when not (StringSet.mem p1.pos_fname !ignored_files) ->
        let shorts = RangeMap.find_opt (p1, p2) !seen_warnings |> Option.value ~default:[] in
        if not (List.exists (fun s -> s = short_str) shorts) then (
          prerr_endline
            (Util.("Warning" |> yellow |> clear)
            ^ ": " ^ short_str
            ^ (if short_str <> "" then " " else "")
            ^ loc_to_string l ^ explanation ^ "\n"
            );
          seen_warnings := RangeMap.add (p1, p2) (short_str :: shorts) !seen_warnings
        )
    | _ -> prerr_endline (Util.("Warning" |> yellow |> clear) ^ ": " ^ short_str ^ "\n" ^ explanation ^ "\n")
  )

let format_warn ?once_from short_str l explanation =
  let already_shown =
    match once_from with
    | Some (file, lnum, cnum, enum) ->
        let key = Printf.sprintf "%d:%d:%d:%s" lnum cnum enum file in
        if StringSet.mem key !once_from_warnings then true
        else (
          once_from_warnings := StringSet.add key !once_from_warnings;
          false
        )
    | None -> false
  in
  if !opt_warnings && not already_shown then (
    match simp_loc l with
    | Some (p1, p2) when not (StringSet.mem p1.pos_fname !ignored_files) ->
        let shorts = RangeMap.find_opt (p1, p2) !seen_warnings |> Option.value ~default:[] in
        if not (List.exists (fun s -> s = short_str) shorts) then (
          let open Error_format in
          prerr_endline (Util.("Warning" |> yellow |> clear) ^ ": " ^ short_str);
          format_message (Location ("", None, l, explanation)) err_formatter;
          seen_warnings := RangeMap.add (p1, p2) (short_str :: shorts) !seen_warnings
        )
    | _ -> prerr_endline (Util.("Warning" |> yellow |> clear) ^ ": " ^ short_str ^ "\n")
  )

let simple_warn str = warn str Parse_ast.Unknown ""

let get_sail_dir default_sail_dir =
  match Sys.getenv_opt "SAIL_DIR" with
  | Some path -> path
  | None ->
      if Sys.file_exists default_sail_dir then default_sail_dir
      else
        raise
          (err_general Parse_ast.Unknown
             ("Sail share directory " ^ default_sail_dir
            ^ " does not exist. Make sure Sail is installed correctly, or try setting the SAIL_DIR environment variable"
             )
          )

let system_checked ?loc:(l = Parse_ast.Unknown) cmd =
  match Unix.system cmd with
  | WEXITED 0 -> ()
  | WEXITED n -> raise (err_general l (Printf.sprintf "Command %s failed with exit code %d" cmd n))
  | WSTOPPED n -> raise (err_general l (Printf.sprintf "Command %s stopped by signal %d" cmd n))
  | WSIGNALED n -> raise (err_general l (Printf.sprintf "Command %s killed by signal %d" cmd n))
