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

open Regex

let parse_regex str =
  let lexbuf = Lexing.from_string str in
  try Some (Regex_parser.regex_eof Regex_lexer.token lexbuf) with
  | _ -> None

let rec string_of_regex =
  let posix_char = function
    | ('.' | '[' | ']' | '{' | '}' | '(' | ')' | '\\' | '*' | '+' | '?' | '|' | '^' | '$') as c -> "\\\\" ^ String.make 1 c
    | c -> String.make 1 c
  in
  let string_of_repeat = function
    | At_least 0 -> "*"
    | At_least 1 -> "+"
    | At_least n -> Printf.sprintf "{,%d}" n
    | Between (0, 1) -> "?"
    | Between (n, m) -> Printf.sprintf "{%d,%d}" n m
    | Exactly n -> Printf.sprintf "{%d}" n
  in
  let string_of_char_class = function
    | Class_char c -> String.make 1 c
    | Class_range (c1, c2) -> String.make 1 c1 ^ "-" ^ String.make 1 c2
  in
  function
  | Group r -> "(" ^ string_of_regex r ^ ")"
  | Or (r1, r2) -> string_of_regex r1 ^ "|" ^ string_of_regex r2
  | Seq rs -> Util.string_of_list "" string_of_regex rs
  | Repeat (r, repeat) -> string_of_regex r ^ string_of_repeat repeat
  | Dot -> "."
  | Char c -> posix_char c
  | Class (true, cc) -> "[" ^ Util.string_of_list "" string_of_char_class cc ^ "]"
  | Class (false, cc) -> "[^" ^ Util.string_of_list "" string_of_char_class cc ^ "]"

let rec ocaml_regex' =
  let posix_char = function
    | ('.' | '[' | ']' | '{' | '}' | '\\' | '*' | '+' | '?' | '|' | '^' | '$') as c -> "\\" ^ String.make 1 c
    | c -> String.make 1 c
  in
  let string_of_repeat = function
    | At_least 0 -> "*"
    | At_least 1 -> "+"
    | At_least n -> Printf.sprintf "{,%d}" n
    | Between (0, 1) -> "?"
    | Between (n, m) -> Printf.sprintf "{%d,%d}" n m
    | Exactly n -> Printf.sprintf "{%d}" n
  in
  let string_of_char_class = function
    | Class_char c -> String.make 1 c
    | Class_range (c1, c2) -> String.make 1 c1 ^ "-" ^ String.make 1 c2
  in
  function
  | Group r -> "\\(" ^ ocaml_regex' r ^ "\\)"
  | Or (r1, r2) -> ocaml_regex' r1 ^ "|" ^ ocaml_regex' r2
  | Seq rs -> Util.string_of_list "" ocaml_regex' rs
  | Repeat (r, repeat) -> ocaml_regex' r ^ string_of_repeat repeat
  | Dot -> "."
  | Char c -> posix_char c
  | Class (true, cc) -> "[" ^ Util.string_of_list "" string_of_char_class cc ^ "]"
  | Class (false, cc) -> "[^" ^ Util.string_of_list "" string_of_char_class cc ^ "]"

let ocaml_regex r = "^" ^ ocaml_regex' r ^ "$" |> Str.regexp_case_fold
