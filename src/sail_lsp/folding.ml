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

open Libsail

(* Folding is computed by lexing the buffer, so it works on a file that is
   mid-edit and does not parse. We fold two things: the region delimited by a
   pair of matching brackets, and a multi-line block comment. *)

(* Bracket families, tracked so a closing bracket folds back to its matching
   opener; an unmatched bracket in a mid-edit buffer is then discarded rather
   than folding across unrelated code. *)
type bracket = Curly | Square | Paren | CurlyBar | SquareBar

let opening : Token.token -> bracket option = function
  | Token.Lcurly -> Some Curly
  | Token.Lsquare -> Some Square
  | Token.Lparen -> Some Paren
  | Token.LcurlyBar -> Some CurlyBar
  | Token.LsquareBar -> Some SquareBar
  | _ -> None

let closing : Token.token -> bracket option = function
  | Token.Rcurly -> Some Curly
  | Token.Rsquare -> Some Square
  | Token.Rparen -> Some Paren
  | Token.RcurlyBar -> Some CurlyBar
  | Token.RsquareBar -> Some SquareBar
  | _ -> None

(* Only a range covering more than one line is worth folding; [start_line] stays
   visible and the client collapses the lines up to and including [end_line]. *)
let add_range ?kind ~start_line ~end_line ranges =
  if end_line > start_line then Lsp.Types.FoldingRange.create ~startLine:start_line ~endLine:end_line ?kind () :: ranges
  else ranges

(* Fold each matching bracket pair back to its opener. A closing bracket pops
   the stack down to the nearest opener of the same family, dropping any
   still-open brackets of other families above it (an unbalanced buffer). *)
let bracket_ranges handle comments contents =
  let lexbuf = Lexing.from_string contents in
  lexbuf.lex_curr_p <- { Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 };
  let ranges = ref [] in
  let stack = ref [] in
  let region = Lsp.Types.FoldingRangeKind.Region in
  ( try
      let continue = ref true in
      while !continue do
        let tok = Lexer.token handle comments lexbuf in
        let line = lexbuf.lex_start_p.pos_lnum - 1 in
        match tok with
        | Token.Eof -> continue := false
        | _ -> (
            match opening tok with
            | Some b -> stack := (b, line) :: !stack
            | None -> (
                match closing tok with
                | None -> ()
                | Some b ->
                    let rec pop = function
                      | (b', start_line) :: rest when b' = b ->
                          ranges := add_range ~kind:region ~start_line ~end_line:line !ranges;
                          rest
                      | _ :: rest -> pop rest
                      | [] -> []
                    in
                    stack := pop !stack
              )
          )
      done
    with _ -> ()
  );
  !ranges

(* Fold every multi-line block comment; single-line and line comments have
   nothing to collapse. *)
let comment_ranges comments =
  let comment = Lsp.Types.FoldingRangeKind.Comment in
  List.fold_left
    (fun ranges (Lexer.Comment (comment_type, s, e, _)) ->
      match comment_type with
      | Parse_ast.Comment_line -> ranges
      | Parse_ast.Comment_block ->
          let { Sail_file.Position.pos_lnum = sl; _ } = s in
          let { Sail_file.Position.pos_lnum = el; _ } = e in
          add_range ~kind:comment ~start_line:(sl - 1) ~end_line:(el - 1) ranges
    )
    [] comments

let compute handle =
  let contents = Sail_file.contents handle in
  (* Lexing collects the comments as a side effect into [comments]. *)
  let comments = ref [] in
  let brackets = bracket_ranges handle comments contents in
  List.rev_append (comment_ranges !comments) brackets
