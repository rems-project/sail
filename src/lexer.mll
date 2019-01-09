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
open Parser
module Big_int = Nat_big_num
open Parse_ast
module M = Map.Make(String)
exception LexError of string * Lexing.position

let r = fun s -> s (* Ulib.Text.of_latin1 *)
(* Available as Scanf.unescaped since OCaml 4.0 but 3.12 is still common *)
let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

let mk_operator prec n op =
  match prec, n with
  | Infix, 0 -> Op0 op
  | Infix, 1 -> Op1 op
  | Infix, 2 -> Op2 op
  | Infix, 3 -> Op3 op
  | Infix, 4 -> Op4 op
  | Infix, 5 -> Op5 op
  | Infix, 6 -> Op6 op
  | Infix, 7 -> Op7 op
  | Infix, 8 -> Op8 op
  | Infix, 9 -> Op9 op
  | InfixL, 0 -> Op0l op
  | InfixL, 1 -> Op1l op
  | InfixL, 2 -> Op2l op
  | InfixL, 3 -> Op3l op
  | InfixL, 4 -> Op4l op
  | InfixL, 5 -> Op5l op
  | InfixL, 6 -> Op6l op
  | InfixL, 7 -> Op7l op
  | InfixL, 8 -> Op8l op
  | InfixL, 9 -> Op9l op
  | InfixR, 0 -> Op0r op
  | InfixR, 1 -> Op1r op
  | InfixR, 2 -> Op2r op
  | InfixR, 3 -> Op3r op
  | InfixR, 4 -> Op4r op
  | InfixR, 5 -> Op5r op
  | InfixR, 6 -> Op6r op
  | InfixR, 7 -> Op7r op
  | InfixR, 8 -> Op8r op
  | InfixR, 9 -> Op9r op
  | _, _ -> assert false

let operators = ref
  (List.fold_left
     (fun r (x, y) -> M.add x y r)
     M.empty
     [ ("/", mk_operator InfixL 7 "/");
       ("%", mk_operator InfixL 7 "%");
     ])

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
     ("function",                (fun x -> Function_));
     ("mapping",                 (fun _ -> Mapping));
     ("overload",                (fun _ -> Overload));
     ("throw",                   (fun _ -> Throw));
     ("try",                     (fun _ -> Try));
     ("catch",                   (fun _ -> Catch));
     ("if",                      (fun x -> If_));
     ("in",			 (fun x -> In));
     ("inc",                     (fun _ -> Inc));
     ("let",                     (fun x -> Let_));
     ("var",                     (fun _ -> Var));
     ("ref",                     (fun _ -> Ref));
     ("Int",                     (fun x -> Int));
     ("Order",                   (fun x -> Order));
     ("Bool",                    (fun x -> Bool));
     ("pure",                    (fun x -> Pure));
     ("register",		 (fun x -> Register));
     ("return",                  (fun x -> Return));
     ("scattered",               (fun x -> Scattered));
     ("sizeof",                  (fun x -> Sizeof));
     ("constant",                (fun x -> Constant));
     ("constraint",              (fun x -> Constraint));
     ("struct",                  (fun x -> Struct));
     ("then",                    (fun x -> Then));
     ("true",                    (fun x -> True));
     ("Type",                    (fun x -> TYPE));
     ("type",		         (fun x -> Typedef));
     ("undefined",               (fun x -> Undefined));
     ("union",			 (fun x -> Union));
     ("newtype",                 (fun x -> Newtype));
     ("with",                    (fun x -> With));
     ("val",                     (fun x -> Val));
     ("repeat",                  (fun _ -> Repeat));
     ("until",                   (fun _ -> Until));
     ("while",                   (fun _ -> While));
     ("do",                      (fun _ -> Do));
     ("mutual",                  (fun _ -> Mutual));
     ("bitfield",                (fun _ -> Bitfield));
     ("where",                   (fun _ -> Where));

     ("barr",                    (fun x -> Barr));
     ("depend",                  (fun x -> Depend));
     ("rreg",                    (fun x -> Rreg));
     ("wreg",                    (fun x -> Wreg));
     ("rmem",                    (fun x -> Rmem));
     ("rmemt",                   (fun x -> Rmemt));
     ("wmem",                    (fun x -> Wmem));
     ("wmv",                     (fun x -> Wmv));
     ("wmvt",                    (fun x -> Wmvt));
     ("eamem",                   (fun x -> Eamem));
     ("exmem",                   (fun x -> Exmem));
     ("undef",                   (fun x -> Undef));
     ("unspec",                  (fun x -> Unspec));
     ("nondet",                  (fun x -> Nondet));
     ("escape",                  (fun x -> Escape));
     ("configuration",           (fun _ -> Configuration));
     ("termination_measure",     (fun _ -> TerminationMeasure));
   ]



}

let ws = [' ''\t']+
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
    { Lexing.new_line lexbuf;
      token lexbuf }
  | "&"					{ (Amp(r"&")) }
  | "@"                                 { (At "@") }
  | "2" ws "^"                          { TwoCaret }
  | "^"					{ (Caret(r"^")) }
  | "::"                                { ColonColon(r "::") }
  (* | "^^"                                { CaretCaret(r "^^") } *)
  | "~~"                                { TildeTilde(r "~~") }
  | ":"                                 { Colon(r ":") }
  | ","                                 { Comma }
  | ".."                                { DotDot }
  | "."                                 { Dot }
  | "=="                                { EqEq(r"==") }
  | "="                                 { (Eq(r"=")) }
  | ">"					{ (Gt(r">")) }
  | "-"					{ Minus }
  | "<"					{ (Lt(r"<")) }
  | "+"					{ (Plus(r"+")) }
  | ";"                                 { Semi }
  | "*"                                 { (Star(r"*")) }
  | "_"                                 { Under }
  | "[|"                                { LsquareBar }
  | "|]"                                { RsquareBar }
  | "{|"                                { LcurlyBar }
  | "|}"                                { RcurlyBar }
  | "|"                                 { Bar }
  | "{"                                 { Lcurly }
  | "}"                                 { Rcurly }
  | "()"                                { Unit(r"()") }
  | "("                                 { Lparen }
  | ")"                                 { Rparen }
  | "["                                 { Lsquare }
  | "]"                                 { Rsquare }
  | "!="				{ (ExclEq(r"!=")) }
  | ">="				{ (GtEq(r">=")) }
  | "->"                                { MinusGt }
  | "<->"                               { Bidir }
  | "<-"                                { LtMinus }
  | "=>"                                { EqGt(r "=>") }
  | "<="				{ (LtEq(r"<=")) }
  | "/*!"       { Doc (doc_comment (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) 0 lexbuf) }
  | "//"        { line_comment (Lexing.lexeme_start_p lexbuf) lexbuf; token lexbuf }
  | "/*"        { comment (Lexing.lexeme_start_p lexbuf) 0 lexbuf; token lexbuf }
  | "*/"        { raise (LexError("Unbalanced comment", Lexing.lexeme_start_p lexbuf)) }
  | "$" (ident+ as i) (lchar* as f) "\n"
    { Lexing.new_line lexbuf; Pragma(i, String.trim f) }
  | "infix" ws (digit as p) ws (operator as op)
    { operators := M.add op (mk_operator Infix (int_of_string (Char.escaped p)) op) !operators;
      Fixity (Infix, Big_int.of_string (Char.escaped p), op) }
  | "infixl" ws (digit as p) ws (operator as op)
    { operators := M.add op (mk_operator InfixL (int_of_string (Char.escaped p)) op) !operators;
      Fixity (InfixL, Big_int.of_string (Char.escaped p), op) }
  | "infixr" ws (digit as p) ws (operator as op)
    { operators := M.add op (mk_operator InfixR (int_of_string (Char.escaped p)) op) !operators;
      Fixity (InfixR, Big_int.of_string (Char.escaped p), op) }
  | operator as op
    { try M.find op !operators
      with Not_found -> raise (LexError ("Operator fixity undeclared " ^ op, Lexing.lexeme_start_p lexbuf)) }
  | tyvar_start startident ident* as i  { TyVar(r i) }
  | "~"                                 { Id(r"~") }
  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) ()
					  (* else if
                                            List.mem i default_type_names ||
                                            List.mem i !custom_type_names then
					    TyId(r i) *)
					  else Id(r i) }
  | (digit+ as i1) "." (digit+ as i2)     { (Real (i1 ^ "." ^ i2)) }
  | "-" (digit* as i1) "." (digit+ as i2) { (Real ("-" ^ i1 ^ "." ^ i2)) }
  | digit+ as i                           { (Num(Big_int.of_string i)) }
  | "-" digit+ as i                       { (Num(Big_int.of_string i)) }
  | "0b" (binarydigit+ as i)              { (Bin(Util.string_of_list "" (fun s -> s) (Util.split_on_char '_' i))) }
  | "0x" (hexdigit+ as i)                 { (Hex(Util.string_of_list "" (fun s -> s) (Util.split_on_char '_' i))) }
  | '"'                                   { (String(
					     string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf)) }
  | eof                                   { Eof }
  | _  as c                               { raise (LexError(
                                            Printf.sprintf "Unexpected character: %c" c,
                                            Lexing.lexeme_start_p lexbuf)) }

and line_comment pos = parse
  | "\n"                                { Lexing.new_line lexbuf; () }
  | _                                   { line_comment pos lexbuf }
  | eof                                 { raise (LexError("File ended before newline in comment", pos)) }

and doc_comment pos b depth = parse
  | "/*!"                               { doc_comment pos b  (depth + 1) lexbuf }
  | "/*"                                { doc_comment pos b (depth + 1) lexbuf }
  | "*/"                                { if depth = 0 then Buffer.contents b
					  else if depth > 0 then doc_comment pos b (depth - 1) lexbuf
					  else assert false }
  | eof                                 { raise (LexError("Unbalanced comment", pos)) }
  | "\n"                                { Buffer.add_string b "\n"; Lexing.new_line lexbuf; doc_comment pos b depth lexbuf }
  | _ as c                              { Buffer.add_string b (String.make 1 c); doc_comment pos b depth lexbuf }

and comment pos depth = parse
  | "/*"                                { comment pos (depth+1) lexbuf }
  | "*/"                                { if depth = 0 then ()
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
  | '\\'                                { assert false (*raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                            "illegal backslash escape in string"*) }
  | '"'                                 { let s = unescaped(Buffer.contents b) in
                                          (*try Ulib.UTF8.validate s; s
                                          with Ulib.UTF8.Malformed_code ->
                                            raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                              "String literal is not valid utf8"))) *) s }
  | eof                                 { assert false (*raise (Reporting.Fatal_error (Reporting.Err_syntax (pos,
                                            "String literal not terminated")))*) }
