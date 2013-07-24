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
open Parser
module M = Map.Make(String)
exception LexError of char * Lexing.position

let r = fun s -> s (* Ulib.Text.of_latin1 *)
(* Available as Scanf.unescaped since OCaml 4.0 but 3.12 is still common *)
let unescaped s = Scanf.sscanf ("\"" ^ s ^ "\"") "%S%!" (fun x -> x)

let kw_table = 
  List.fold_left
    (fun r (x,y) -> M.add x y r)
    M.empty
    [
     ("and",                     (fun x -> And(x)));
     ("as",                      (fun x -> As(x)));
     ("case",			 (fun x -> Case(x)));
     ("clause",                  (fun x -> Clause(x)));
     ("const",			 (fun x -> Const(x)));
     ("default",		 (fun x -> Default(x)));
     ("effect",                  (fun x -> Effect(x)));
     ("Effects",                 (fun x -> Effects(x)));
     ("end",                     (fun x -> End(x)));
     ("enum",			 (fun x -> Enum(x)));
     ("else",                    (fun x -> Else(x)));
     ("false",                   (fun x -> False(x)));
     ("forall",                  (fun x -> Forall(x)));
     ("function",                (fun x -> Function_(x)));
     ("if",                      (fun x -> If_(x)));
     ("in",			 (fun x -> In(x)));
     ("IN",                      (fun x -> IN(x)));     
     ("let",                     (fun x -> Let_(x)));
     ("member",                  (fun x -> Member(x)));
     ("Nat",                     (fun x -> Nat(x)));
     ("Order",                   (fun x -> Order(x)));
     ("rec",			 (fun x -> Rec(x)));
     ("register",		 (fun x -> Register(x)));
     ("scattered",               (fun x -> Scattered(x)));
     ("struct",                  (fun x -> Struct(x)));
     ("switch",			 (fun x -> Switch(x)));
     ("then",                    (fun x -> Then(x)));
     ("true",                    (fun x -> True(x)));
     ("type",                    (fun x -> Type(x)));
     ("Type",                    (fun x -> TYPE(x)));
     ("typedef",		 (fun x -> Typedef(x)));
     ("union",			 (fun x -> Union(x)));
     ("with",                    (fun x -> With(x)));
     ("val",                     (fun x -> Val(x)));

     ("AND",			 (fun x -> AND(x)));
     ("div",			 (fun x -> Div_(x)));
     ("EOR",			 (fun x -> EOR(x)));
     ("mod",			 (fun x -> Mod(x)));
     ("OR",			 (fun x -> OR(x)));
     ("quot",			 (fun x -> Quot(x)));
     ("rem",			 (fun x -> Rem(x)));
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
let oper_char = ['!''$''%''&''*''+''-''.''/'':''<''=''>''?''@''^''|''~']
let safe_com1 = [^'*''('')''\n']
let safe_com2 = [^'*''(''\n']
let com_help = "("*safe_com2 | "*"*"("+safe_com2 | "*"*safe_com1
let com_body = com_help*"*"*
let escape_sequence = ('\\' ['\\''\"''\'''n''t''b''r']) | ('\\' digit digit digit) | ('\\' 'x' hexdigit hexdigit)

rule token skips = parse
  | ws as i
    { token (Parse_ast.Ws(r i)::skips) lexbuf }
  | "\n"
    { Lexing.new_line lexbuf;
      token (Parse_ast.Nl::skips) lexbuf } 
  
  | "&"					{ (Amp(Some(skips),r"&")) }
  | "@"					{ (At(Some(skips),r"@")) }
  | "|"                                 { (Bar(Some(skips))) }
  | "^"					{ (Carrot(Some(skips),r"^")) }
  | ":"                                 { (Colon(Some(skips))) }
  | ","                                 { (Comma(Some(skips))) }
  | "."                                 { (Dot(Some(skips))) }
  | "/"			                { (Div(Some(skips),r"/")) }
  | "="                                 { (Eq(Some(skips),r"=")) }
  | "!"					{ (Excl(Some(skips),r"!")) }
  | ">"					{ (Gt(Some(skips),r">")) }
  | "-"					{ (Minus(Some(skips))) }
  | "<"					{ (Lt(Some(skips),r"<")) }
  | "+"					{ (Plus(Some(skips),r"+")) }
  | ";"                                 { (Semi(Some(skips))) }
  | "*"                                 { (Star(Some(skips),r"*")) }
  | "~"					{ (Tilde(Some(skips),r"~")) }
  | "_"                                 { (Under(Some(skips))) }
  | "{"                                 { (Lcurly(Some(skips))) }
  | "}"                                 { (Rcurly(Some(skips))) }
  | "("                                 { (Lparen(Some(skips))) }
  | ")"                                 { (Rparen(Some(skips))) }
  | "["                                 { (Lsquare(Some(skips))) }
  | "]"                                 { (Rsquare(Some(skips))) }
  | "&&" as i                           { (AmpAmp(Some(skips),r i)) }
  | "||"                                { (BarBar(Some(skips))) }
  | "|>"                                { (BarGt(Some(skips))) }
  | "|]"				{ (BarSquare(Some(skips))) }
  | "^^"				{ (CarrotCarrot(Some(skips),r"^^")) }
  | "::" as i                           { (ColonColon(Some(skips),r i)) }
  | ".."				{ (DotDot(Some(skips))) }  
  | "=/="				{ (EqDivEq(Some(skips),r"=/=")) }
  | "=="				{ (EqEq(Some(skips),r"==")) }
  | "!="				{ (ExclEq(Some(skips),r"!=")) }
  | "!!"				{ (ExclExcl(Some(skips),r"!!")) }
  | ">="				{ (GtEq(Some(skips),r">=")) }
  | ">=+"				{ (GtEqPlus(Some(skips),r">=+")) }
  | ">>"				{ (GtGt(Some(skips),r">>")) }
  | ">>>"				{ (GtGtGt(Some(skips),r">>")) }
  | ">+"				{ (GtPlus(Some(skips),r">+")) }
  | "#>>"				{ (HashGtGt(Some(skips),r"#>>")) }
  | "#<<"				{ (HashLtLt(Some(skips),r"#<<")) }
  | "->"                                { (MinusGt(Some(skips))) }
  | "<="				{ (LtEq(Some(skips),r"<=")) }
  | "<=+"				{ (LtEqPlus(Some(skips),r"<=+")) }
  | "<>"				{ (LtGt(Some(skips),r"<>")) }
  | "<<"				{ (LtLt(Some(skips),r"<<")) }
  | "<<<"				{ (LtLtLt(Some(skips),r"<<<")) }
  | "<+"				{ (LtPlus(Some(skips),r"<+")) }
  | "**"				{ (StarStar(Some(skips),r"**")) }
  | "~^"				{ (TildeCarrot(Some(skips),r"~^")) }

  | ">=_s"				{ (GtEqUnderS(Some(skips),r">=_s")) }
  | ">=_si"				{ (GtEqUnderSi(Some(skips),r">=_si")) }
  | ">=_u"				{ (GtEqUnderU(Some(skips),r">=_u")) }
  | ">=_ui"				{ (GtEqUnderUi(Some(skips),r">=_ui")) }
  | ">>_u"				{ (GtGtUnderU(Some(skips),r">>_u")) }
  | ">_s"				{ (GtUnderS(Some(skips),r">_s")) }
  | ">_si"				{ (GtUnderSi(Some(skips),r">_si")) }
  | ">_u"				{ (GtUnderU(Some(skips),r">_u")) }
  | ">_ui"				{ (GtUnderUi(Some(skips),r">_ui")) }
  | "<=_s"				{ (LtEqUnderS(Some(skips),r"<=_s")) }
  | "<=_si"				{ (LtEqUnderSi(Some(skips),r"<=_si")) }
  | "<=_u"				{ (LtEqUnderU(Some(skips),r"<=_u")) }
  | "<=_ui"				{ (LtEqUnderUi(Some(skips),r"<=_ui")) }
  | "<_s"				{ (LtUnderS(Some(skips),r"<_s")) }
  | "<_si"				{ (LtUnderSi(Some(skips),r"<_si")) }
  | "<_u"				{ (LtUnderU(Some(skips),r"<_u")) }
  | "<_ui"				{ (LtUnderUi(Some(skips),r"<_ui")) }
  | "**_s"				{ (StarStarUnderS(Some(skips),r"**_s")) }
  | "**_si"				{ (StarStarUnderSi(Some(skips),r"**_si")) }
  | "*_u"				{ (StarUnderU(Some(skips),r"*_u")) }
  | "*_ui"				{ (StarUnderUi(Some(skips),r"*_ui")) }
  | "2^"				{ (TwoCarrot(Some(skips),r"2^")) }


  | "--"                           
    { token (Parse_ast.Com(Parse_ast.Comment(comment lexbuf))::skips) lexbuf }

  | startident ident* as i              { if M.mem i kw_table then
                                            (M.find i kw_table) (Some(skips))
                                          else
                                            Id(Some(skips), r i) }
  | "&" oper_char+ as i                 { (AmpI(Some(skips),r i)) }
  | "@" oper_char+ as i                 { (AtI(Some(skips),r i)) }
  | "^" oper_char+ as i                 { (CarrotI(Some(skips),r i)) }
  | "/" oper_char+ as i                 { (DivI(Some(skips),r i)) }
  | "=" oper_char+ as i			{ (EqI(Some(skips),r i)) }
  | "!" oper_char+ as i                 { (ExclI(Some(skips),r i)) }
  | ">" oper_char+ as i                 { (GtI(Some(skips),r i)) }
  | "<" oper_char+ as i			{ (LtI(Some(skips),r i)) }
  | "+"	oper_char+ as i			{ (PlusI(Some(skips),r i)) }
  | "*" oper_char+ as i                 { (StarI(Some(skips),r i)) }
  | "~"	oper_char+ as i			{ (TildeI(Some(skips),r i)) }
  | "&&" oper_char+ as i                { (AmpAmpI(Some(skips),r i)) }
  | "^^" oper_char+ as i		{ (CarrotCarrotI(Some(skips),r i)) }
  | "::" oper_char+ as i                { (ColonColonI(Some(skips),r i)) }
  | "=/=" oper_char+ as i		{ (EqDivEqI(Some(skips),r i)) }
  | "==" oper_char+ as i		{ (EqEqI(Some(skips),r i)) }
  | "!=" oper_char+ as i		{ (ExclEqI(Some(skips),r i)) }
  | "!!" oper_char+ as i		{ (ExclExclI(Some(skips),r i)) }
  | ">=" oper_char+ as i		{ (GtEqI(Some(skips),r i)) }
  | ">=+" oper_char+ as i		{ (GtEqPlusI(Some(skips),r i)) }
  | ">>" oper_char+ as i		{ (GtGtI(Some(skips),r i)) }
  | ">>>" oper_char+ as i		{ (GtGtGtI(Some(skips),r i)) }
  | ">+" oper_char+ as i		{ (GtPlusI(Some(skips),r i)) }
  | "#>>" oper_char+ as i		{ (HashGtGt(Some(skips),r i)) }
  | "#<<" oper_char+ as i		{ (HashLtLt(Some(skips),r i)) }
  | "<=" oper_char+ as i		{ (LtEqI(Some(skips),r i)) }
  | "<=+" oper_char+ as i		{ (LtEqPlusI(Some(skips),r i)) }
  | "<<" oper_char+ as i		{ (LtLtI(Some(skips),r i)) }
  | "<<<" oper_char+ as i		{ (LtLtLtI(Some(skips),r i)) }
  | "<+" oper_char+ as i		{ (LtPlusI(Some(skips),r i)) }
  | "**" oper_char+ as i		{ (StarStarI(Some(skips),r i)) }
  | "~^" oper_char+ as i		{ (TildeCarrot(Some(skips),r i)) }

  | ">=_s" oper_char+ as i				{ (GtEqUnderSI(Some(skips),r i)) }
  | ">=_si" oper_char+ as i				{ (GtEqUnderSiI(Some(skips),r i)) }
  | ">=_u" oper_char+ as i				{ (GtEqUnderUI(Some(skips),r i)) }
  | ">=_ui" oper_char+ as i				{ (GtEqUnderUiI(Some(skips),r i)) }
  | ">>_u" oper_char+ as i				{ (GtGtUnderUI(Some(skips),r i)) }
  | ">_s" oper_char+ as i				{ (GtUnderSI(Some(skips),r i)) }
  | ">_si" oper_char+ as i				{ (GtUnderSiI(Some(skips),r i)) }
  | ">_u" oper_char+ as i				{ (GtUnderUI(Some(skips),r i)) }
  | ">_ui" oper_char+ as i				{ (GtUnderUiI(Some(skips),r i)) }
  | "<=_s" oper_char+ as i				{ (LtEqUnderSI(Some(skips),r i)) }
  | "<=_si" oper_char+ as i				{ (LtEqUnderSiI(Some(skips),r i)) }
  | "<=_u" oper_char+ as i				{ (LtEqUnderUI(Some(skips),r i)) }
  | "<=_ui" oper_char+ as i				{ (LtEqUnderUiI(Some(skips),r i)) }
  | "<_s" oper_char+ as i				{ (LtUnderSI(Some(skips),r i)) }
  | "<_si" oper_char+ as i				{ (LtUnderSiI(Some(skips),r i)) }
  | "<_u" oper_char+ as i				{ (LtUnderUI(Some(skips),r i)) }
  | "<_ui" oper_char+ as i				{ (LtUnderUiI(Some(skips),r i)) }
  | "**_s" oper_char+ as i				{ (StarStarUnderSI(Some(skips),r i)) }
  | "**_si" oper_char+ as i				{ (StarStarUnderSiI(Some(skips),r i)) }
  | "*_u" oper_char+ as i				{ (StarUnderUI(Some(skips),r i)) }
  | "*_ui" oper_char+ as i				{ (StarUnderUiI(Some(skips),r i)) }
  | "2^" oper_char+ as i				{ (TwoCarrotI(Some(skips),r i)) }
  
  | digit+ as i                         { (Num(Some(skips),int_of_string i)) }
  | "0b" (binarydigit+ as i)		{ (Bin(Some(skips), i)) }
  | "0x" (hexdigit+ as i) 		{ (Hex(Some(skips), i)) }
  | '"'                                 { (String(Some(skips),
                                           string (Lexing.lexeme_start_p lexbuf) (Buffer.create 10) lexbuf)) }
  | eof                                 { (Eof(Some(skips))) }
  | _  as c                             { raise (LexError(c, Lexing.lexeme_start_p lexbuf)) }


and comment = parse
  | (com_body "("* as i) "--"           { let c1 = comment lexbuf in
                                          let c2 = comment lexbuf in
                                            Parse_ast.Chars(r i) :: Parse_ast.Comment(c1) :: c2}
  | (com_body as i) "\n"                { Lexing.new_line lexbuf;
                                          [Parse_ast.Chars(r i)] }
  | _  as c                             { raise (LexError(c, Lexing.lexeme_start_p lexbuf)) }
  | eof                                 { [] }

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
