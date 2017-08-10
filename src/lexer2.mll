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
open Parser2
module M = Map.Make(String)
exception LexError of string * Lexing.position

let r = fun s -> s (* Ulib.Text.of_latin1 *)
(* Available as Scanf.unescaped since OCaml 4.0 but 3.12 is still common *)
let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

let mk_operator n op =
  match n with
  | 0 -> Op0 op
  | 1 -> Op1 op
  | 2 -> Op2 op
  | 3 -> Op3 op
  | 4 -> Op4 op
  | 5 -> Op5 op
  | 6 -> Op6 op
  | 7 -> Op7 op
  | 8 -> Op8 op
  | 9 -> Op9 op

let operators = ref M.empty

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
     ("const",			 (fun _ -> Const));
     ("dec",                     (fun _ -> Dec));
     ("def",                     (fun _ -> Def));
     ("op",                      (fun _ -> Op));
     ("default",		 (fun _ -> Default));
     ("deinfix",                 (fun _ -> Deinfix));
     ("effect",                  (fun _ -> Effect));
     ("Effect",                  (fun _ -> EFFECT));
     ("end",                     (fun _ -> End));
     ("enum",		         (fun _ -> Enum));
     ("else",                    (fun _ -> Else));
     ("exit",                    (fun _ -> Exit));
     ("extern",                  (fun _ -> Extern));
     ("cast",                    (fun _ -> Cast));
     ("false",                   (fun _ -> False));
     ("forall",                  (fun _ -> Forall));
     ("foreach",                 (fun _ -> Foreach));
     ("function",                (fun x -> Function_));
     ("overload",                (fun _ -> Overload));
     ("if",                      (fun x -> If_));
     ("in",			 (fun x -> In));
     ("inc",                     (fun _ -> Inc));
     ("IN",                      (fun x -> IN));
     ("let",                     (fun x -> Let_));
     ("member",                  (fun x -> Member));
     ("Int",                     (fun x -> Int));
     ("Order",                   (fun x -> Order));
     ("pure",                    (fun x -> Pure));
     ("rec",			 (fun x -> Rec));
     ("register",		 (fun x -> Register));
     ("return",                  (fun x -> Return));
     ("scattered",               (fun x -> Scattered));
     ("sizeof",                  (fun x -> Sizeof));
     ("constraint",              (fun x -> Constraint));
     ("struct",                  (fun x -> Struct));
     ("switch",			 (fun x -> Switch));
     ("then",                    (fun x -> Then));
     ("true",                    (fun x -> True));
     ("Type",                    (fun x -> TYPE));
     ("type",		         (fun x -> Typedef));
     ("undefined",               (fun x -> Undefined));
     ("union",			 (fun x -> Union));
     ("with",                    (fun x -> With));
     ("when",                    (fun x -> When));
     ("val",                     (fun x -> Val));

     ("div",			 (fun x -> Div_));
     ("mod",			 (fun x -> Mod));
     ("mod_s",                   (fun x -> ModUnderS));
     ("quot",			 (fun x -> Quot));
     ("quot_s",                  (fun x -> QuotUnderS));
     ("rem",			 (fun x -> Rem));

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

]

let default_type_names = ["bool";"unit";"vector";"range";"list";"bit";"nat"; "int"; "real";
			  "uint8";"uint16";"uint32";"uint64";"atom";"implicit";"string";"option"]
let custom_type_names : string list ref = ref []

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
  | "&"					{ (Amp(r"&")) }
  | "|"                                 { Bar }
  | "^"					{ (Carrot(r"^")) }
  | ":"                                 { Colon(r ":") }
  | ","                                 { Comma }
  | "."                                 { Dot }
  | "="                                 { (Eq(r"=")) }
  | ">"					{ (Gt(r">")) }
  | "-"					{ Minus }
  | "<"					{ (Lt(r"<")) }
  | "+"					{ (Plus(r"+")) }
  | ";"                                 { Semi }
  | "*"                                 { (Star(r"*")) }
  | "_"                                 { Under }
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
  | "=>"                                { EqGt(r "=>") }
  | "<="				{ (LtEq(r"<=")) }
  | "infix" ws (digit as p) ws (oper_char+ as op)
    { operators := M.add op (mk_operator (int_of_string (Char.escaped p)) op) !operators;
      token lexbuf }
  | oper_char+ as op
    { try M.find op !operators
      with Not_found -> raise (LexError ("Operator fixity undeclared", Lexing.lexeme_start_p lexbuf)) }
  | "(*"        { comment (Lexing.lexeme_start_p lexbuf) 0 lexbuf; token lexbuf }
  | "*)"        { raise (LexError("Unbalanced comment", Lexing.lexeme_start_p lexbuf)) }
  | (tyvar_start startident ident* as i) ":" { TyDecl(r i) }
  | (startident ident* as i) ":"        { Decl(r i) }
  | tyvar_start startident ident* as i  { TyVar(r i) }
  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) ()
					  (* else if
                                            List.mem i default_type_names ||
                                            List.mem i !custom_type_names then
					    TyId(r i) *)
					  else Id(r i) }
  | (digit+ as i1) "." (digit+ as i2)     { (Real (i1 ^ "." ^ i2)) }
  | "-" (digit* as i1) "." (digit+ as i2) { (Real ("-" ^ i1 ^ "." ^ i2)) }
  | digit+ as i                           { (Num(int_of_string i)) }
  | "-" digit+ as i                       { (Num(int_of_string i)) }
  | "0b" (binarydigit+ as i)              { (Bin(i)) }
  | "0x" (hexdigit+ as i)                 { (Hex(i)) }
  | '"'                                   { (String(
                                             string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf)) }
  | eof                                   { Eof }
  | _  as c                               { raise (LexError(
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
