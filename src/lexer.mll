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
open Parser
open Big_int
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
     ("and",                     (fun _ -> And));
     ("alias",                   (fun _ -> Alias));
     ("as",                      (fun _ -> As));
     ("assert",                  (fun _ -> Assert));
     ("bitzero",                 (fun _ -> Bitzero));
     ("bitone",                  (fun _ -> Bitone));
     ("bits",                    (fun _ -> Bits));
     ("by",                      (fun _ -> By));
     ("case",			 (fun _ -> Case));
     ("clause",                  (fun _ -> Clause));
     ("const",			 (fun _ -> Const));
     ("dec",                     (fun _ -> Dec));
     ("def",                     (fun _ -> Def));
     ("default",		 (fun _ -> Default));
     ("deinfix",                 (fun _ -> Deinfix));
     ("effect",                  (fun _ -> Effect));
     ("Effect",                  (fun _ -> EFFECT));
     ("end",                     (fun _ -> End));
     ("enumerate",		 (fun _ -> Enumerate));
     ("else",                    (fun _ -> Else));
     ("exit",                    (fun _ -> Exit));
     ("extern",                  (fun _ -> Extern));
     ("cast",                    (fun _ -> Cast));
     ("false",                   (fun _ -> False));
     ("try",                     (fun _ -> Try));
     ("catch",                   (fun _ -> Catch));
     ("throw",                   (fun _ -> Throw));
     ("forall",                  (fun _ -> Forall));
     ("exist",                   (fun _ -> Exist));
     ("foreach",                 (fun _ -> Foreach));
     ("function",                (fun x -> Function_));
     ("overload",                (fun _ -> Overload));
     ("if",                      (fun x -> If_));
     ("in",			 (fun x -> In));
     ("inc",                     (fun _ -> Inc));
     ("IN",                      (fun x -> IN));
     ("let",                     (fun x -> Let_));
     ("member",                  (fun x -> Member));
     ("Nat",                     (fun x -> Nat));
     ("Num",                     (fun x -> NatNum));
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
     ("typedef",		 (fun x -> Typedef));
     ("undefined",               (fun x -> Undefined));
     ("union",			 (fun x -> Union));
     ("with",                    (fun x -> With));
     ("when",                    (fun x -> When));
     ("repeat",                  (fun x -> Repeat));
     ("until",                   (fun x -> Until));
     ("while",                   (fun x -> While));
     ("do",                      (fun x -> Do));
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
let ident = alphanum|['_''\'''#']
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
  | "@"					{ (At(r"@")) }
  | "|"                                 { Bar }
  | "^"					{ (Carrot(r"^")) }
  | ":"                                 { Colon(r ":") }
  | ","                                 { Comma }
  | "."                                 { Dot }
  | "="                                 { (Eq(r"=")) }
  | "!"					{ (Excl(r"!")) }
  | ">"					{ (Gt(r">")) }
  | "-"					{ Minus }
  | "<"					{ (Lt(r"<")) }
  | "+"					{ (Plus(r"+")) }
  | ";"                                 { Semi }
  | "*"                                 { (Star(r"*")) }
  | "~"					{ (Tilde(r"~")) }
  | "_"                                 { Under }
  | "{"                                 { Lcurly }
  | "}"                                 { Rcurly }
  | "("                                 { Lparen }
  | ")"                                 { Rparen }
  | "["                                 { Lsquare }
  | "]"                                 { Rsquare }
  | "&&" as i                           { (AmpAmp(r i)) }
  | "||"                                { BarBar }
  | "||]"                               { BarBarSquare }
  | "|]"				{ BarSquare }
  | "^^"				{ (CarrotCarrot(r"^^")) }
  | "::" as i                           { (ColonColon(r i)) }
  | ":="                                { ColonEq }
  | ":>"                                { ColonGt }
  | ":]"                                { ColonSquare }
  | ".."				{ DotDot }
  | "=="				{ (EqEq(r"==")) }
  | "!="				{ (ExclEq(r"!=")) }
  | "!!"				{ (ExclExcl(r"!!")) }
  | ">="				{ (GtEq(r">=")) }
  | ">=+"				{ (GtEqPlus(r">=+")) }
  | ">>"				{ (GtGt(r">>")) }
  | ">>>"				{ (GtGtGt(r">>>")) }
  | ">+"				{ (GtPlus(r">+")) }
  | "#>>"				{ (HashGtGt(r"#>>")) }
  | "#<<"				{ (HashLtLt(r"#<<")) }
  | "->"                                { MinusGt }
  | "<:"                                { LtColon }
  | "<="				{ (LtEq(r"<=")) }
  | "<=+"				{ (LtEqPlus(r"<=+")) }
  | "<>"				{ (LtGt(r"<>")) }
  | "<<"				{ (LtLt(r"<<")) }
  | "<<<"				{ (LtLtLt(r"<<<")) }
  | "<+"				{ (LtPlus(r"<+")) }
  | "**"				{ (StarStar(r"**")) }
  | "[|"                                { SquareBar }
  | "[||"                               { SquareBarBar }
  | "[:"                                { SquareColon }
  | "~^"				{ (TildeCarrot(r"~^")) }

  | "+_s"                               { (PlusUnderS(r"+_s")) }
  | "-_s"                               { (MinusUnderS(r"-_s")) }
  | ">=_s"				{ (GtEqUnderS(r">=_s")) }
  | ">=_si"				{ (GtEqUnderSi(r">=_si")) }
  | ">=_u"				{ (GtEqUnderU(r">=_u")) }
  | ">=_ui"				{ (GtEqUnderUi(r">=_ui")) }
  | ">>_u"				{ (GtGtUnderU(r">>_u")) }
  | ">_s"				{ (GtUnderS(r">_s")) }
  | ">_si"				{ (GtUnderSi(r">_si")) }
  | ">_u"				{ (GtUnderU(r">_u")) }
  | ">_ui"				{ (GtUnderUi(r">_ui")) }
  | "<=_s"				{ (LtEqUnderS(r"<=_s")) }
  | "<=_si"				{ (LtEqUnderSi(r"<=_si")) }
  | "<=_u"				{ (LtEqUnderU(r"<=_u")) }
  | "<=_ui"				{ (LtEqUnderUi(r"<=_ui")) }
  | "<_s"				{ (LtUnderS(r"<_s")) }
  | "<_si"				{ (LtUnderSi(r"<_si")) }
  | "<_u"				{ (LtUnderU(r"<_u")) }
  | "<_ui"				{ (LtUnderUi(r"<_ui")) }
  | "*_s"                               { (StarUnderS(r"*_s")) }
  | "**_s"				{ (StarStarUnderS(r"**_s")) }
  | "**_si"				{ (StarStarUnderSi(r"**_si")) }
  | "*_u"				{ (StarUnderU(r"*_u")) }
  | "*_ui"				{ (StarUnderUi(r"*_ui")) }
  | "2^"				{ (TwoCarrot(r"2^")) }
  | "2**"				{ TwoStarStar }


  | "(*"        { comment (Lexing.lexeme_start_p lexbuf) 0 lexbuf; token lexbuf }
  | "*)"        { raise (LexError("Unbalanced comment", Lexing.lexeme_start_p lexbuf)) }

  | tyvar_start startident ident* as i  { TyVar(r i) }
  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) ()
                                          else if
                                            List.mem i default_type_names ||
                                            List.mem i !custom_type_names then
					    TyId(r i)
                                          else Id(r i) }
  | "&" oper_char+ as i                 { (AmpI(r i)) }
  | "@" oper_char+ as i                 { (AtI(r i)) }
  | "^" oper_char+ as i                 { (CarrotI(r i)) }
  | "/" oper_char+ as i                 { (DivI(r i)) }
  | "=" oper_char+ as i			{ (EqI(r i)) }
  | "!" oper_char+ as i                 { (ExclI(r i)) }
  | ">" oper_char+ as i                 { (GtI(r i)) }
  | "<" oper_char+ as i			{ (LtI(r i)) }
  | "+"	oper_char+ as i			{ (PlusI(r i)) }
  | "*" oper_char+ as i                 { (StarI(r i)) }
  | "~"	oper_char+ as i			{ (TildeI(r i)) }
  | "&&" oper_char+ as i                { (AmpAmpI(r i)) }
  | "^^" oper_char+ as i		{ (CarrotCarrotI(r i)) }
  | "::" oper_char+ as i                { (ColonColonI(r i)) }
  | "==" oper_char+ as i		{ (EqEqI(r i)) }
  | "!=" oper_char+ as i		{ (ExclEqI(r i)) }
  | "!!" oper_char+ as i		{ (ExclExclI(r i)) }
  | ">=" oper_char+ as i		{ (GtEqI(r i)) }
  | ">=+" oper_char+ as i		{ (GtEqPlusI(r i)) }
  | ">>" oper_char+ as i		{ (GtGtI(r i)) }
  | ">>>" oper_char+ as i		{ (GtGtGtI(r i)) }
  | ">+" oper_char+ as i		{ (GtPlusI(r i)) }
  | "#>>" oper_char+ as i		{ (HashGtGt(r i)) }
  | "#<<" oper_char+ as i		{ (HashLtLt(r i)) }
  | "<=" oper_char+ as i		{ (LtEqI(r i)) }
  | "<=+" oper_char+ as i		{ (LtEqPlusI(r i)) }
  | "<<" oper_char+ as i		{ (LtLtI(r i)) }
  | "<<<" oper_char+ as i		{ (LtLtLtI(r i)) }
  | "<+" oper_char+ as i		{ (LtPlusI(r i)) }
  | "**" oper_char+ as i		{ (StarStarI(r i)) }
  | "~^" oper_char+ as i		{ (TildeCarrot(r i)) }

  | ">=_s" oper_char+ as i				{ (GtEqUnderSI(r i)) }
  | ">=_si" oper_char+ as i				{ (GtEqUnderSiI(r i)) }
  | ">=_u" oper_char+ as i				{ (GtEqUnderUI(r i)) }
  | ">=_ui" oper_char+ as i				{ (GtEqUnderUiI(r i)) }
  | ">>_u" oper_char+ as i				{ (GtGtUnderUI(r i)) }
  | ">_s" oper_char+ as i				{ (GtUnderSI(r i)) }
  | ">_si" oper_char+ as i				{ (GtUnderSiI(r i)) }
  | ">_u" oper_char+ as i				{ (GtUnderUI(r i)) }
  | ">_ui" oper_char+ as i				{ (GtUnderUiI(r i)) }
  | "<=_s" oper_char+ as i				{ (LtEqUnderSI(r i)) }
  | "<=_si" oper_char+ as i				{ (LtEqUnderSiI(r i)) }
  | "<=_u" oper_char+ as i				{ (LtEqUnderUI(r i)) }
  | "<=_ui" oper_char+ as i				{ (LtEqUnderUiI(r i)) }
  | "<_s" oper_char+ as i				{ (LtUnderSI(r i)) }
  | "<_si" oper_char+ as i				{ (LtUnderSiI(r i)) }
  | "<_u" oper_char+ as i				{ (LtUnderUI(r i)) }
  | "<_ui" oper_char+ as i				{ (LtUnderUiI(r i)) }
  | "**_s" oper_char+ as i				{ (StarStarUnderSI(r i)) }
  | "**_si" oper_char+ as i				{ (StarStarUnderSiI(r i)) }
  | "*_u" oper_char+ as i				{ (StarUnderUI(r i)) }
  | "*_ui" oper_char+ as i				{ (StarUnderUiI(r i)) }
  | "2^" oper_char+ as i				{ (TwoCarrotI(r i)) }

  | (digit+ as i1) "." (digit+ as i2)     { (Real (i1 ^ "." ^ i2)) }
  | "-" (digit* as i1) "." (digit+ as i2) { (Real ("-" ^ i1 ^ "." ^ i2)) }
  | digit+ as i                           { (Num(big_int_of_string i)) }
  | "-" digit+ as i                       { (Num(big_int_of_string i)) }
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
