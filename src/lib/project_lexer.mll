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

{

open Project
open Project_parser

module M = Map.Make(String)

let kw_table =
  List.fold_left
    (fun r (x, y) -> M.add x y r)
    M.empty
    [
      ("__test",    (fun _ -> Test));
      ("after",     (fun _ -> After));
      ("before",    (fun _ -> Before));
      ("default",   (fun _ -> Default));
      ("directory", (fun _ -> Directory));
      ("else",      (fun _ -> Else));
      ("false",     (fun _ -> False));
      ("files",     (fun _ -> Files));
      ("if",        (fun _ -> If));
      ("optional",  (fun _ -> Optional));
      ("requires",  (fun _ -> Requires));
      ("then",      (fun _ -> Then));
      ("true",      (fun _ -> True));
      ("variable",  (fun _ -> Variable));
      ("import",    (fun p -> raise (Reporting.err_lex p "import is a reserved keyword")));
      ("namespace", (fun p -> raise (Reporting.err_lex p "namespace is a reserved keyword")));
      ("open",      (fun p -> raise (Reporting.err_lex p "open is a reserved keyword")));
      ("use",       (fun p -> raise (Reporting.err_lex p "use is a reserved keyword")));
      ("versions",  (fun p -> raise (Reporting.err_lex p "versions is a reserved keyword")));
    ]

}

let wsc = [' ''\t']
let ws = wsc+
let letter = ['a'-'z''A'-'Z']
let digit = ['0'-'9']
let hexdigit = ['0'-'9''A'-'F''a'-'f''_']
let alphanum = letter|digit
let startident = letter|'_'
let ident = alphanum|'_'

let oper_char = ['!''%''&''*''+''-''.''/'':''<''=''>''@''^''|']
let oper_char_no_slash = ['!''%''&''*''+''-''.'':''<''=''>''@''^''|']
let oper_char_no_slash_star = ['!''%''&''+''-''.'':''<''=''>''@''^''|']
let operator1 = oper_char
let operator2 = oper_char oper_char_no_slash_star | oper_char_no_slash oper_char
let operatorn = oper_char oper_char_no_slash_star (oper_char* ('_' ident)?) | oper_char_no_slash oper_char (oper_char* ('_' ident)?) | oper_char ('_' ident)?
let operator = operator1 | operator2 | operatorn
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)

rule token = parse
  | ws                                { token lexbuf }
  | "\n"
  | "\r\n"                            { Lexing.new_line lexbuf; token lexbuf }
  | ","                               { Comma }
  | "("                               { Lparen }
  | ")"                               { Rparen }
  | "["                               { Lsquare }
  | "]"                               { Rsquare }
  | "{"                               { Lcurly }
  | "}"                               { Rcurly }
  | "=="                              { EqEq }
  | "!="                              { ExclEq }
  | ">="                              { GtEq }
  | "<="                              { LtEq }
  | "="                               { Eq }
  | ">"                               { Gt }
  | "<"                               { Lt }
  | "/"                               { Slash }
  | ";"                               { Semi }
  | "$" (ident+ as v)                 { Var v }
  | ".."                              { DotDot }
  | (startident ident* as i) wsc* "{" { let p = Lexing.lexeme_start_p lexbuf in
                                        IdLcurly (i, { p with pos_cnum = p.pos_cnum + String.length i}) }
  | ident* ".sail" as f               { FileId f }
  | startident ident* as i            { match M.find_opt i kw_table with
                                        | Some kw -> kw (Lexing.lexeme_start_p lexbuf)
                                        | None -> Id i }
  | '"'                               { let startpos = Lexing.lexeme_start_p lexbuf in
                                        let contents = string startpos (Buffer.create 10) lexbuf in
                                        lexbuf.lex_start_p <- startpos;
                                        String(contents) }
  | eof                               { Eof }
  | _  as c                           { raise (Reporting.err_lex
                                          (Lexing.lexeme_start_p lexbuf)
                                          (Printf.sprintf "Unexpected character: %s" (Char.escaped c))) }
  | "//"
    { line_comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf; token lexbuf }
  | "/*"
    { comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) 0 lexbuf; token lexbuf }
  | "*/"
    { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "Unbalanced comment") }

and line_comment pos b = parse
  | "\n"                              { Lexing.new_line lexbuf }
  | _ as c                            { Buffer.add_string b (String.make 1 c); line_comment pos b lexbuf }
  | eof                               { raise (Reporting.err_lex pos "File ended before newline in comment") }

and comment pos b depth = parse
  | "/*"                              { comment pos b (depth + 1) lexbuf }
  | "*/"                              { if depth > 0 then (
                                          comment pos b (depth-1) lexbuf
                                        ) }
  | "\n"                              { Buffer.add_string b "\n";
                                        Lexing.new_line lexbuf;
                                        comment pos b depth lexbuf }
  | _ as c                            { Buffer.add_string b (String.make 1 c); comment pos b depth lexbuf }
  | eof                               { raise (Reporting.err_lex pos "Unbalanced comment") }

and string pos b = parse
  | ([^'"''\n''\\']*'\n' as i)          { Lexing.new_line lexbuf;
                                          Buffer.add_string b i;
                                          string pos b lexbuf }
  | ([^'"''\n''\\']* as i)              { Buffer.add_string b i; string pos b lexbuf }
  | escape_sequence as i                { Buffer.add_string b i; string pos b lexbuf }
  | '\\' '\n' ws                        { Lexing.new_line lexbuf; string pos b lexbuf }
  | '\\'                                { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "String literal contains illegal backslash escape sequence") }
  | '"'                                 { Scanf.unescaped (Buffer.contents b) }
  | eof                                 { raise (Reporting.err_lex pos "String literal not terminated") }
