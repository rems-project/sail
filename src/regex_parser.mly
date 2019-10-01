/**************************************************************************/
/*     Sail                                                               */
/*                                                                        */
/*  Copyright (c) 2013-2017                                               */
/*    Kathyrn Gray                                                        */
/*    Shaked Flur                                                         */
/*    Stephen Kell                                                        */
/*    Gabriel Kerneis                                                     */
/*    Robert Norton-Wright                                                */
/*    Christopher Pulte                                                   */
/*    Peter Sewell                                                        */
/*    Alasdair Armstrong                                                  */
/*    Brian Campbell                                                      */
/*    Thomas Bauereiss                                                    */
/*    Anthony Fox                                                         */
/*    Jon French                                                          */
/*    Dominic Mulligan                                                    */
/*    Stephen Kell                                                        */
/*    Mark Wassell                                                        */
/*                                                                        */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/**************************************************************************/

%{

open Regex

%}

/* POSIX extended regular expression special characters are .[{}()\*+?|$ */
%token Dot Lsquare Lcurly Rcurly Lparen Rparen Backslash Star Plus Question Bar Dollar
/* Tokens that are usually mapped to themselves, except in certain contexts ^,]- */
%token Caret Comma Rsquare Dash
%token Eof
%token <char> Char
%token <string> Int

%start regex_eof
%type <Regex.regex> regex_eof

%%

/* Precedence from lowest to highest:
   - Alternation |
   - Anchoring ^$ (which we don't parse)
   - Concatenation
   - Repetition * + ? {n} {n,} {m,n}
   - Grouping ()
   - Character sets []
*/

regex_alt:
  | regex_concat
    { $1 }
  | regex_concat Bar regex_alt
    { Or ($1, $3) }

regex_concat:
  | regex_repeat
    { $1 }
  | regex_repeat regex_concat
    { Seq [$1; $2] }

regex_repeat:
/* Quantifiers ? + and * */
  | regex_group Question
    { Regex.Repeat ($1, Regex.Between (0, 1)) }
  | regex_group Plus
    { Regex.Repeat ($1, Regex.At_least 1) }
  | regex_group Star
    { Regex.Repeat ($1, Regex.At_least 0) }

/* R{n} R{n,} and R{n,m} */
  | regex_group Lcurly Int Rcurly
    { Regex.Repeat ($1, Regex.Exactly (int_of_string $3)) }
  | regex_group Lcurly Int Comma Rcurly
    { Regex.Repeat ($1, Regex.At_least (int_of_string $3)) }
  | regex_group Lcurly Int Comma Int Rcurly
    { Regex.Repeat ($1, Regex.Between (int_of_string $3, int_of_string $5)) }

  | regex_group
    { $1 }

regex_group:
  | Lparen regex_alt Rparen
    { Regex.Group $2 }
  | Dot
    { Regex.Dot }
  | Char
    { Regex.Char $1 }
  | Comma
    { Regex.Char ',' }
  | Dash
    { Regex.Char '-' }
  | Lsquare cclass
    { Regex.Class (true, $2) }
  | Lsquare Caret cclass
    { Regex.Class (false, $3) }
  | Backslash escaped
    { Regex.Char $2 }

cclass:
  | Char cclass
    { Regex.Class_char $1 :: $2 }
  | Char Dash Char cclass
    { Regex.Class_range ($1, $3) :: $4 }
  | Dash Rsquare
    { [Regex.Class_char '-'] }
  | Rsquare
    { [] }

escaped:
  | Dot { '.' }
  | Lsquare { '[' }
  | Rsquare { ']' }
  | Lcurly { '{' }
  | Rcurly { '}' }
  | Lparen { '(' }
  | Rparen { ')' }
  | Caret { '^' }
  | Dollar { '$' }
  | Backslash { '\\' }
  | Star { '*' }
  | Plus { '+' }
  | Question { '?' }
  | Bar { '|' }

regex_eof:
  | regex_alt Eof
    { $1 }
