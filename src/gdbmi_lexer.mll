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

{

open Gdbmi_parser

let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

}

let ws = [' ''\t']+
let letter = ['a'-'z''A'-'Z''?']
let digit = ['0'-'9']
let hexdigit = ['0'-'9''A'-'F''a'-'f']
let alphanum = letter|digit
let startident = letter
let ident = alphanum|['-']
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)

rule token = parse
  | ws
    { token lexbuf }
  | "\n"
    { Lexing.new_line lexbuf;
      token lexbuf }
  | "="					{ Eq }
  | "["                                 { Lsquare }
  | "]"                                 { Rsquare }
  | "{"                                 { Lcurly }
  | "}"                                 { Rcurly }
  | ","                                 { Comma }
  | "^"                                 { Caret }
  | digit+ as i                         { Num (int_of_string i) }
  | startident ident* as i              { Id i }
  | '"'                                 { String (string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf) }
  | eof                                 { Eof }

and string pos b = parse
  | ([^'"''\n''\\']*'\n' as i)          { Lexing.new_line lexbuf;
                                          Buffer.add_string b i;
                                          string pos b lexbuf }
  | ([^'"''\n''\\']* as i)              { Buffer.add_string b i; string pos b lexbuf }
  | escape_sequence as i                { Buffer.add_string b i; string pos b lexbuf }
  | '\\' '\n' ws                        { Lexing.new_line lexbuf; string pos b lexbuf }
  | '\\'                                { assert false (*raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                            "illegal backslash escape in string"*) }
  | '"'                                 { let s = unescaped(Buffer.contents b) in
                                          (*try Ulib.UTF8.validate s; s
                                          with Ulib.UTF8.Malformed_code ->
                                            raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                              "String literal is not valid utf8"))) *) s }
  | eof                                 { assert false (*raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                            "String literal not terminated")))*) }