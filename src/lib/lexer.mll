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
open Parser
module Big_int = Nat_big_num
open Parse_ast
module M = Map.Make(String)

(* Available as Scanf.unescaped since OCaml 4.0 but 3.12 is still common *)
let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

let kw_table =
  List.fold_left
    (fun r (x,y) -> M.add x y r)
    M.empty
    [
     ("and",                     (fun _ -> And));
     ("as",                      (fun _ -> As));
     ("assert",                  (fun _ -> Assert));
     ("bitzero",                 (fun _ -> Bitzero));
     ("bitone",                  (fun _ -> Bitone));
     ("by",                      (fun _ -> By));
     ("match",			 (fun _ -> Match));
     ("clause",                  (fun _ -> Clause));
     ("dec",                     (fun _ -> Dec));
     ("operator",                (fun _ -> Op));
     ("default",		 (fun _ -> Default));
     ("effect",                  (fun _ -> Effect));
     ("end",                     (fun _ -> End));
     ("enum",		         (fun _ -> Enum));
     ("else",                    (fun _ -> Else));
     ("exit",                    (fun _ -> Exit));
     ("cast",                    (fun _ -> Cast));
     ("false",                   (fun _ -> False));
     ("forall",                  (fun _ -> Forall));
     ("foreach",                 (fun _ -> Foreach));
     ("function",                (fun _ -> Function_));
     ("mapping",                 (fun _ -> Mapping));
     ("overload",                (fun _ -> Overload));
     ("throw",                   (fun _ -> Throw));
     ("try",                     (fun _ -> Try));
     ("catch",                   (fun _ -> Catch));
     ("if",                      (fun _ -> If_));
     ("in",			 (fun _ -> In));
     ("inc",                     (fun _ -> Inc));
     ("let",                     (fun _ -> Let_));
     ("var",                     (fun _ -> Var));
     ("ref",                     (fun _ -> Ref));
     ("Int",                     (fun _ -> Int));
     ("Order",                   (fun _ -> Order));
     ("Bool",                    (fun _ -> Bool));
     ("pure",                    (fun _ -> Pure));
     ("monadic",                 (fun _ -> Monadic));
     ("register",		 (fun _ -> Register));
     ("return",                  (fun _ -> Return));
     ("scattered",               (fun _ -> Scattered));
     ("sizeof",                  (fun _ -> Sizeof));
     ("constraint",              (fun _ -> Constraint));
     ("constant",                (fun _ -> Constant));
     ("struct",                  (fun _ -> Struct));
     ("then",                    (fun _ -> Then));
     ("true",                    (fun _ -> True));
     ("Type",                    (fun _ -> TYPE));
     ("type",		         (fun _ -> Typedef));
     ("undefined",               (fun _ -> Undefined));
     ("union",			 (fun _ -> Union));
     ("newtype",                 (fun _ -> Newtype));
     ("with",                    (fun _ -> With));
     ("val",                     (fun _ -> Val));
     ("outcome",                 (fun _ -> Outcome));
     ("instantiation",           (fun _ -> Instantiation));
     ("impl",                    (fun _ -> Impl));
     ("import",                  (fun p -> raise (Reporting.err_lex p "import is a reserved keyword")));
     ("module",                  (fun p -> raise (Reporting.err_lex p "module is a reserved keyword")));
     ("repeat",                  (fun _ -> Repeat));
     ("until",                   (fun _ -> Until));
     ("while",                   (fun _ -> While));
     ("do",                      (fun _ -> Do));
     ("mutual",                  (fun _ -> Mutual));
     ("bitfield",                (fun _ -> Bitfield));
     ("barr",                    (fun _ -> Barr));
     ("depend",                  (fun _ -> Depend));
     ("rreg",                    (fun _ -> Rreg));
     ("wreg",                    (fun _ -> Wreg));
     ("rmem",                    (fun _ -> Rmem));
     ("rmemt",                   (fun _ -> Rmem));
     ("wmem",                    (fun _ -> Wmem));
     ("wmv",                     (fun _ -> Wmv));
     ("wmvt",                    (fun _ -> Wmv));
     ("eamem",                   (fun _ -> Eamem));
     ("exmem",                   (fun _ -> Exmem));
     ("undef",                   (fun _ -> Undef));
     ("unspec",                  (fun _ -> Unspec));
     ("nondet",                  (fun _ -> Nondet));
     ("escape",                  (fun _ -> Escape));
     ("configuration",           (fun _ -> Configuration));
     ("termination_measure",     (fun _ -> TerminationMeasure));
     ("forwards",                (fun _ -> Forwards));
     ("backwards",               (fun _ -> Backwards));
     ("internal_plet",           (fun _ -> InternalPLet));
     ("internal_return",         (fun _ -> InternalReturn));
     ("internal_assume",         (fun _ -> InternalAssume));
   ]

type comment_type = Comment_block | Comment_line

type comment =
  | Comment of comment_type * Lexing.position * Lexing.position * string

let comments = ref []

}

let wsc = [' ''\t']
let ws = wsc+
let letter = ['a'-'z''A'-'Z''?']
let digit = ['0'-'9']
let binarydigit = ['0'-'1''_']
let hexdigit = ['0'-'9''A'-'F''a'-'f''_']
let alphanum = letter|digit
let startident = letter|'_'
let ident = alphanum|['_''\'''#']
let tyvar_start = '\''
(* Ensure an operator cannot start with comment openings *)
let oper_char = ['!''%''&''*''+''-''.''/'':''<''=''>''@''^''|']
let oper_char_no_slash = ['!''%''&''*''+''-''.'':''<''=''>''@''^''|']
let oper_char_no_slash_star = ['!''%''&''+''-''.'':''<''=''>''@''^''|']
let operator1 = oper_char
let operator2 = oper_char oper_char_no_slash_star | oper_char_no_slash oper_char
let operatorn = oper_char oper_char_no_slash_star (oper_char* ('_' ident)?) | oper_char_no_slash oper_char (oper_char* ('_' ident)?) | oper_char ('_' ident)?
let operator = operator1 | operator2 | operatorn
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)
let lchar = [^'\n']

rule token = parse
  | ws
    { token lexbuf }
  | "\n"
  | "\r\n"
    { Lexing.new_line lexbuf;
      token lexbuf }
  | "@"                                 { At }
  | "2" ws "^"                          { TwoCaret }
  | "^"					{ Caret }
  | "::"                                { ColonColon }
  | ":"                                 { Colon ":" }
  | ","                                 { Comma }
  | ".."                                { DotDot }
  | "."                                 { Dot }
  | "="                                 { Eq "=" }
  | ";"                                 { Semi }
  | "*"                                 { Star }
  | "_"                                 { Under }
  | "[|"                                { LsquareBar }
  | "|]"                                { RsquareBar }
  | "{|"                                { LcurlyBar }
  | "|}"                                { RcurlyBar }
  | "|"                                 { Bar }
  | "{"                                 { Lcurly }
  | "}"                                 { Rcurly }
  | "()"                                { Unit "()" }
  | "("                                 { Lparen }
  | ")"                                 { Rparen }
  | "["                                 { Lsquare }
  | "]"                                 { Rsquare }
  | "->"                                { MinusGt }
  | "-"                                 { Minus }
  | "<->"                               { Bidir }
  | "=>"                                { EqGt "=>" }
  | "/*!"       { Doc (doc_comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) 0 false lexbuf) }
  | "//"        { line_comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf; token lexbuf }
  | "/*"        { comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) 0 lexbuf; token lexbuf }
  | "*/"        { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "Unbalanced comment") }
  | "$[" (ident+ as i)
    { let attr = attribute 0 (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf in Attribute(i, String.trim attr) }
  | "$" (ident+ as i)
    { let p = pragma (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) false lexbuf in Pragma(i, String.trim p) }
  | "infix" ws (digit as p) ws (operator as op)
    { Fixity (Infix, Big_int.of_string (Char.escaped p), op) }
  | "infixl" ws (digit as p) ws (operator as op)
    { Fixity (InfixL, Big_int.of_string (Char.escaped p), op) }
  | "infixr" ws (digit as p) ws (operator as op)
    { Fixity (InfixR, Big_int.of_string (Char.escaped p), op) }
  | operator as op                        { OpId op }
  | tyvar_start startident ident* as i    { TyVar i }
  | "~"                                   { Id "~" }
  | startident ident* as i                { if M.mem i kw_table then
                                              (M.find i kw_table) (Lexing.lexeme_start_p lexbuf)
					    else
                                              Id i }
  | (digit+ as i1) "." (digit+ as i2)     { Real (i1 ^ "." ^ i2) }
  | "-" (digit* as i1) "." (digit+ as i2) { Real ("-" ^ i1 ^ "." ^ i2) }
  | digit+ as i                           { Num (Big_int.of_string i) }
  | "-" digit+ as i                       { Num (Big_int.of_string i) }
  | "0b" (binarydigit+ as i)              { Bin (Util.string_of_list "" (fun s -> s) (Util.split_on_char '_' i)) }
  | "0x" (hexdigit+ as i)                 { Hex (Util.string_of_list "" (fun s -> s) (Util.split_on_char '_' i)) }
  | '"'                                   { let startpos = Lexing.lexeme_start_p lexbuf in
                                            let contents = string startpos (Buffer.create 10) lexbuf in
                                            lexbuf.lex_start_p <- startpos;
                                            String(contents) }
  | eof                                   { Eof }
  | _  as c                               { raise (Reporting.err_lex
                                              (Lexing.lexeme_start_p lexbuf)
                                              (Printf.sprintf "Unexpected character: %s" (Char.escaped c))) }

and attribute depth pos b = parse
  | "["                                 { Buffer.add_char b '['; attribute (depth + 1) pos b lexbuf }
  | "]"                                 { if depth = 0 then Buffer.contents b else (Buffer.add_char b ']'; attribute (depth - 1) pos b lexbuf) }
  | "\n"                                { Buffer.add_char b '\n'; Lexing.new_line lexbuf; attribute depth pos b lexbuf }
  | "//"                                { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "Line comment is not allowed within an attribute") }
  | "/*"                                { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "Block comment is not allowed within an attribute") }
  | _ as c                              { Buffer.add_char b c; attribute depth pos b lexbuf }
  | eof                                 { raise (Reporting.err_lex pos "File ended before this attribute has been closed") }

(* The after_block logic here allows a pragma to end with either a
line comment or a block comment, but the pragma cannot continue after
a block comment. This ensures that `$pragma fo/* comment */o` is not
allowed (it would otherwise have value `foo`) *)

and pragma pos b after_block = parse
  | "\n"                                { Lexing.new_line lexbuf; Buffer.contents b }
  | (wsc as c)                          { Buffer.add_string b (String.make 1 c); pragma pos b after_block lexbuf }
  | "//"                                { line_comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf; unescaped (Buffer.contents b) }
  | "/*"                                { comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) 0 lexbuf; pragma pos b true lexbuf }
  | _ as c                              { if after_block then
                                            raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "Directive continued after block comment")
                                          else (
                                            Buffer.add_string b (String.make 1 c);
                                            pragma pos b after_block lexbuf
                                          ) }
  | eof                                 { raise (Reporting.err_lex pos "File ended before newline in directive") }

and line_comment pos b = parse
  | "\n"                                { Lexing.new_line lexbuf;
                                          comments := Comment (Comment_line, pos, Lexing.lexeme_end_p lexbuf, Buffer.contents b) :: !comments }
  | _ as c                              { Buffer.add_string b (String.make 1 c); line_comment pos b lexbuf }
  | eof                                 { raise (Reporting.err_lex pos "File ended before newline in comment") }

and doc_comment pos b depth lstart = parse
  | "/*!"                               { Buffer.add_string b "/*!"; doc_comment pos b (depth + 1) false lexbuf }
  | "/*"                                { Buffer.add_string b "/*"; doc_comment pos b (depth + 1) false lexbuf }
  | "*/"                                { if depth = 0 then Buffer.contents b
					  else (
                                            Buffer.add_string b "*/";
                                            doc_comment pos b (depth - 1) false lexbuf
					  ) }
  | "\n"                                { Buffer.add_string b "\n"; Lexing.new_line lexbuf; doc_comment pos b depth true lexbuf }
  | wsc+ "*" wsc as prefix              { if lstart then (
                                            Buffer.add_string b (String.make (String.length prefix - 3) ' ');
                                            doc_comment pos b depth false lexbuf
                                          ) else (
                                            Buffer.add_string b prefix; doc_comment pos b depth false lexbuf
                                          ) }
  | _ as c                              { Buffer.add_string b (String.make 1 c); doc_comment pos b depth false lexbuf }
  | eof                                 { raise (Reporting.err_lex pos "Unbalanced documentation comment") }

and comment pos b depth = parse
  | "/*"                                { comment pos b (depth + 1) lexbuf }
  | "*/"                                { if depth = 0 then (
                                            comments := Comment (Comment_block, pos, Lexing.lexeme_end_p lexbuf, Buffer.contents b) :: !comments
                                          ) else (
                                            comment pos b (depth-1) lexbuf
                                          ) }
  | "\n"                                { Buffer.add_string b "\n"; 
                                          Lexing.new_line lexbuf;
                                          comment pos b depth lexbuf }
  | _ as c                              { Buffer.add_string b (String.make 1 c); comment pos b depth lexbuf }
  | eof                                 { raise (Reporting.err_lex pos "Unbalanced comment") }

and string pos b = parse
  | ([^'"''\n''\\']*'\n' as i)          { Lexing.new_line lexbuf;
                                          Buffer.add_string b i;
                                          string pos b lexbuf }
  | ([^'"''\n''\\']* as i)              { Buffer.add_string b i; string pos b lexbuf }
  | escape_sequence as i                { Buffer.add_string b i; string pos b lexbuf }
  | '\\' '\n' ws                        { Lexing.new_line lexbuf; string pos b lexbuf }
  | '\\'                                { raise (Reporting.err_lex (Lexing.lexeme_start_p lexbuf) "String literal contains illegal backslash escape sequence") }
  | '"'                                 { unescaped (Buffer.contents b) }
  | eof                                 { raise (Reporting.err_lex pos "String literal not terminated") }
