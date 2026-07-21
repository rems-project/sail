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

let legend =
  Lsp.Types.SemanticTokensLegend.create ~tokenModifiers:[]
    ~tokenTypes:["keyword"; "type"; "typeParameter"; "comment"; "string"; "number"; "operator"; "variable"; "macro"]

let legend_index h =
  let open Token.Highlight in
  match h with
  | H_id -> Some 7
  | H_keyword -> Some 0
  | H_kind -> Some 1
  | H_comment -> Some 3
  | H_string -> Some 4
  | H_pragma -> Some 8
  | H_internal -> Some 8
  | H_operator -> Some 6
  | H_literal -> Some 5
  | H_ty_var -> Some 2
  | H_bracket | H_punctuation -> None

(* A token span in byte coordinates: zero-based start/end lines, byte columns
   within those lines, end column exclusive. *)
type span = { s_line : int; s_col : int; e_line : int; e_col : int; kind : Token.Highlight.t }

let span_of_lexing (s : Lexing.position) (e : Lexing.position) kind =
  {
    s_line = s.pos_lnum - 1;
    s_col = s.pos_cnum - s.pos_bol;
    e_line = e.pos_lnum - 1;
    e_col = e.pos_cnum - e.pos_bol;
    kind;
  }

let span_of_position (s : Sail_file.position) (e : Sail_file.position) kind =
  let { Sail_file.Position.pos_lnum = sl; pos_bol = sb; pos_cnum = sc; _ } = s in
  let { Sail_file.Position.pos_lnum = el; pos_bol = eb; pos_cnum = ec; _ } = e in
  { s_line = sl - 1; s_col = sc - sb; e_line = el - 1; e_col = ec - eb; kind }

(* Lex the whole file, returning token spans in source order followed by the
   spans of the (non-doc) comments the lexer collects separately. A lex error in
   a buffer that is mid-edit stops the scan, keeping whatever was recognised. *)
let raw_spans handle contents =
  let comments = ref [] in
  let lexbuf = Lexing.from_string contents in
  lexbuf.lex_curr_p <- { Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = 0 };
  let spans = ref [] in
  ( try
      let continue = ref true in
      while !continue do
        match Token.Highlight.classify (Lexer.token handle comments lexbuf) with
        | Some kind -> spans := span_of_lexing lexbuf.lex_start_p lexbuf.lex_curr_p kind :: !spans
        | None -> continue := false
      done
    with _ -> ()
  );
  let comment_spans =
    List.rev_map (fun (Lexer.Comment (_, s, e, _)) -> span_of_position s e Token.Highlight.H_comment) !comments
  in
  List.rev_append !spans comment_spans

(* One emitted token, in UTF-16 coordinates: zero-based line, start character and
   length in UTF-16 code units, and its type. *)
type token = { line : int; start : int; length : int; kind : Token.Highlight.t }

let line_length lines i = if i >= 0 && i < Array.length lines then String.length lines.(i) else 0

(* Convert the byte range [b0, b1) on line [i] to a UTF-16 token, or [None] if
   the line is out of range or the range is empty (e.g. a blank line inside a
   block comment). *)
let utf16_token lines i b0 b1 kind =
  if i < 0 || i >= Array.length lines then None
  else (
    let line = lines.(i) in
    let len = String.length line in
    let b0 = max 0 (min b0 len) in
    let b1 = max b0 (min b1 len) in
    if b1 <= b0 then None
    else (
      let start = Sail_file.utf16_length (String.sub line 0 b0) in
      let length = Sail_file.utf16_length (String.sub line b0 (b1 - b0)) in
      Some { line = i; start; length; kind }
    )
  )

(* The LSP encoding forbids a token from spanning several lines, so split a span
   into one token per line it covers. *)
let split lines (span : span) acc =
  let push i b0 b1 acc = match utf16_token lines i b0 b1 span.kind with Some t -> t :: acc | None -> acc in
  if span.e_line <= span.s_line then push span.s_line span.s_col span.e_col acc
  else (
    let acc = ref (push span.s_line span.s_col (line_length lines span.s_line) acc) in
    for i = span.s_line + 1 to span.e_line - 1 do
      acc := push i 0 (line_length lines i) !acc
    done;
    push span.e_line 0 span.e_col !acc
  )

let compare_token t1 t2 = if t1.line <> t2.line then compare t1.line t2.line else compare t1.start t2.start

(* Delta-encode the sorted tokens into the flat integer array the LSP expects:
   five integers per token [deltaLine; deltaStart; length; tokenType; modifiers],
   each position relative to the previous token. We emit no modifiers. *)
let encode tokens =
  let sorted = List.sort compare_token (List.filter (fun t -> t.length > 0) tokens) in
  let rec go prev_line prev_start = function
    | [] -> []
    | t :: rest -> (
        match legend_index t.kind with
        (* A token the LSP legend has no entry for (punctuation, brackets) is not
         emitted, so it must not advance the delta cursor: the client only sees
         emitted tokens and measures deltas relative to the previous one. *)
        | None -> go prev_line prev_start rest
        | Some index ->
            let delta_line = t.line - prev_line in
            let delta_start = if delta_line = 0 then t.start - prev_start else t.start in
            delta_line :: delta_start :: t.length :: index :: 0 :: go t.line t.start rest
      )
  in
  Array.of_list (go 0 0 sorted)

let compute handle =
  let contents = Sail_file.contents handle in
  let lines = Array.of_list (String.split_on_char '\n' contents) in
  let tokens = List.fold_left (fun acc span -> split lines span acc) [] (raw_spans handle contents) in
  Lsp.Types.SemanticTokens.create ~data:(encode tokens) ()
