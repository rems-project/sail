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

{
open Pre_parser
module M = Map.Make(String)
exception LexError of string * Lexing.position

let r = fun s -> s (* Ulib.Text.of_latin1 *)
(* Available as Scanf.unescaped since OCaml 4.0 but 3.12 is still common *)
let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

let kw_table =
  List.fold_left
    (fun r (x,y) -> M.add x y r)
    M.empty
    [
     ("and",                     (fun _ -> Other));
     ("as",                      (fun _ -> Other));
     ("bits",                    (fun _ -> Other));
     ("by",                      (fun _ -> Other));
     ("case",			 (fun _ -> Other));
     ("clause",                  (fun _ -> Other));
     ("const",			 (fun _ -> Other));
     ("dec",                     (fun _ -> Other));
     ("default",		 (fun _ -> Other));
     ("deinfix",                 (fun _ -> Other));
     ("effect",                  (fun _ -> Other));
     ("Effects",                 (fun _ -> Other));
     ("end",                     (fun _ -> Other));
     ("enumerate",		 (fun _ -> Other));
     ("else",                    (fun _ -> Other));
     ("extern",                  (fun _ -> Other));
     ("false",                   (fun _ -> Other));
     ("forall",                  (fun _ -> Other));
     ("foreach",                 (fun _ -> Other));
     ("function",                (fun x -> Other));
     ("if",                      (fun x -> Other));
     ("in",			 (fun x -> Other));
     ("IN",                      (fun x -> Other));
     ("Inc",                     (fun x -> Other));
     ("let",                     (fun x -> Other));
     ("member",                  (fun x -> Other));
     ("Nat",                     (fun x -> Other));
     ("Order",                   (fun x -> Other));
     ("pure",                    (fun x -> Other));
     ("rec",			 (fun x -> Other));
     ("register",		 (fun x -> Other));
     ("scattered",               (fun x -> Other));
     ("struct",                  (fun x -> Other));
     ("switch",			 (fun x -> Other));
     ("then",                    (fun x -> Other));
     ("true",                    (fun x -> Other));
     ("Type",                    (fun x -> Other));
     ("typedef",		 (fun x -> Typedef));
     ("undefined",               (fun x -> Other));
     ("union",			 (fun x -> Other));
     ("with",                    (fun x -> Other));
     ("val",                     (fun x -> Other));

     ("AND",			 (fun x -> Other));
     ("div",			 (fun x -> Other));
     ("EOR",			 (fun x -> Other));
     ("mod",			 (fun x -> Other));
     ("OR",			 (fun x -> Other));
     ("quot",			 (fun x -> Other));
     ("rem",			 (fun x -> Other));
]

}

let ws = [' ''\t']+
let letter = ['a'-'z''A'-'Z']
let digit = ['0'-'9']
let binarydigit = ['0'-'1']
let hexdigit = ['0'-'9''A'-'F''a'-'f']
let alphanum = letter|digit
let startident = letter|'_'
let ident = alphanum|['_''\'']
let tyvar_start = '\''
let oper_char = ['!''$''%''&''*''+''-''.''/'':''<''=''>''?''@''^''|''~']
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)

rule token = parse
  | ws
    { token lexbuf }
  | "\n"
    { Lexing.new_line lexbuf;
      token lexbuf }

  | "2**" | "&"	| "@" | "|" | "^" | ":"  | "," | "."  | "/" | "=" | "!" | ">" | "-" | "<" |
    "+" | ";" | "*" | "~" | "_" | "{" | "}" | "(" | ")" | "[" | "]" | "&&" | "||" | "|]" | "||]" |
    "^^" | "::" | ":>" |  ":=" | ".." | "=/=" | "==" | "!=" | "!!" | ">=" | ">=+" | ">>" | ">>>" | ">+" |
    "#>>" | "#<<" | "->" | "<:" | "<="	| "<=+"	| "<>" | "<<" | "<<<" | "<+" | "**" | "~^" | ">=_s" |
    ">=_si" | ">=_u" | ">=_ui" | ">>_u" | ">_s" | ">_si" | ">_u" | ">_ui" | "<=_s" | "<=_si" |
    "<=_u" | "<=_ui" | "<_s" | "<_si" | "<_u" | "<_ui" | "**_s" | "**_si" | "*_u" | "*_ui"| "2^"				{ Other }


  | "(*"        { comment (Lexing.lexeme_start_p lexbuf) 0 lexbuf; token lexbuf }
  | "*)"        { raise (LexError("Unbalanced comment", Lexing.lexeme_start_p lexbuf)) }

  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) ()
                                          else
                                            Id(r i) }
  | tyvar_start startident ident* as i   { Other }
  | "&" oper_char+ | "@" oper_char+  | "^" oper_char+ | "/" oper_char+ | "=" oper_char+ |
    "!" oper_char+ | ">" oper_char+  | "<" oper_char+ | "+" oper_char+ | "*" oper_char+ |
    "~"	oper_char+ | "&&" oper_char+ | "^^" oper_char+| "::" oper_char+| "=/=" oper_char+ |
    "==" oper_char+ | "!=" oper_char+ | "!!" oper_char+ | ">=" oper_char+ | ">=+" oper_char+ |
    ">>" oper_char+ | ">>>" oper_char+ | ">+" oper_char+ | "#>>" oper_char+ | "#<<" oper_char+ |
    "<=" oper_char+ | "<=+" oper_char+ | "<<" oper_char+ | "<<<" oper_char+ | "<+" oper_char+ | 
    "**" oper_char+ | "~^" oper_char+ | ">=_s" oper_char+ | ">=_si" oper_char+ | ">=_u" oper_char+ |
    ">=_ui" oper_char+ | ">>_u" oper_char+ | ">_s" oper_char+ | ">_si" oper_char+| ">_u" oper_char+ |
    ">_ui" oper_char+ | "<=_s" oper_char+ | "<=_si" oper_char+ | "<=_u" oper_char+ | "<=_ui" oper_char+ |
    "<_s" oper_char+ | "<_si" oper_char+ | "<_u" oper_char+ | "<_ui" oper_char+ | "**_s" oper_char+ |
    "**_si" oper_char+ | "*_u" oper_char+ | "*_ui" oper_char+ | "2^" oper_char+  { Other }			
  | digit+ as i                         { Other }
  | "0b" (binarydigit+ as i)		{ Other }
  | "0x" (hexdigit+ as i) 		{ Other }
  | '"'                                 { let _ = string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf in Other }
  | eof                                 { Eof }
  | _  as c                             { raise (LexError(
                                          Printf.sprintf "Unexpected character: %c" c,
                                          Lexing.lexeme_start_p lexbuf)) }


and comment pos depth = parse
  | "(*"                                { comment pos (depth+1) lexbuf }
  | "*)"                                { if depth = 0 then ()
                                          else if depth > 0 then comment pos (depth-1) lexbuf
                                          else assert false }
  | "\n"                                { Lexing.new_line lexbuf;
                                          comment pos depth lexbuf }
  | '"'                                 { ignore(string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf);
                                          comment pos depth lexbuf }
  | _                                   { comment pos depth lexbuf }
  | eof                                 { raise (LexError("Unbalanced comment", pos)) }

and string pos b = parse
  | ([^'"''\n''\\']*'\n' as i)          { Lexing.new_line lexbuf;
                                          Buffer.add_string b i;
                                          string pos b lexbuf }
  | ([^'"''\n''\\']* as i)              { Buffer.add_string b i; string pos b lexbuf }
  | escape_sequence as i                { Buffer.add_string b i; string pos b lexbuf }
  | '\\' '\n' ws                        { Lexing.new_line lexbuf; string pos b lexbuf }
  | '\\'                                { assert false (*raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                            "illegal backslash escape in string"*) }
  | '"'                                 { let s = unescaped(Buffer.contents b) in
                                          (*try Ulib.UTF8.validate s; s
                                          with Ulib.UTF8.Malformed_code ->
                                            raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                              "String literal is not valid utf8"))) *) s }
  | eof                                 { assert false (*raise (Reporting_basic.Fatal_error (Reporting_basic.Err_syntax (pos,
                                            "String literal not terminated")))*) }
