/****************************************************************************/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*  1. Redistributions of source code must retain the above copyright       */
/*     notice, this list of conditions and the following disclaimer.        */
/*  2. Redistributions in binary form must reproduce the above copyright    */
/*     notice, this list of conditions and the following disclaimer in      */
/*     the documentation and/or other materials provided with the           */
/*     distribution.                                                        */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      */
/*  SUCH DAMAGE.                                                            */
/****************************************************************************/

%{

[@@@coverage exclude_file]

open Project

let span x s e = (x, (s, e))

%}

%token After Before Directory If Then Else Requires Files Default Optional Variable Test True False
%token Comma DotDot Eq Gt Lt EqEq GtEq LtEq ExclEq Slash Semi
%token Lparen Rparen Lsquare Rsquare Lcurly Rcurly
%token Eof

%token <string> FileId
%token <string> Id
%token <string * Lexing.position> IdLcurly
%token <string> String
%token <string> Var

%start file
%type <Project.def spanned list> file

%%

exp:
  | e = op_exp
    { e }
  | If; i = exp; Then; t = op_exp; Else; e = exp
    { span (E_if (i, t, e)) $startpos $endpos }

exp_list:
  | x = exp; Comma?
    { [x] }
  | x = exp; Comma; xs = exp_list
    { x :: xs }

exp_non_empty:
  | x = exp; Comma?
    { (x, []) }
  | x = exp; Comma; xs = exp_list
    { (x, xs) }

exp_comma_block:
  | es = exp_non_empty
    { es }
  | Lcurly; es = exp_non_empty; Rcurly
    { es }

%inline comparison:
  | EqEq
    { "==" }
  | GtEq
    { "<=" }
  | LtEq
    { ">=" }
  | Gt
    { ">" }
  | Lt
    { "<" }
  | ExclEq
    { "!=" }

op_exp:
  | lhs = slash_exp; o = comparison; rhs = slash_exp
    { span (E_op (lhs, o, rhs)) $startpos $endpos }
  | e = slash_exp
    { e }

slash_exp:
  | lhs = atomic_exp; Slash; rhs = slash_exp
    { span (E_op (lhs, "/", rhs)) $startpos $endpos }
  | e = atomic_exp
    { e }

atomic_exp:
  | True
    { span (E_value (bool_value true)) $startpos $endpos }
  | False
    { span (E_value (bool_value false)) $startpos $endpos }
  | f = FileId
    { span (E_file f) $startpos $endpos }
  | id = Id
    { span (E_id id) $startpos $endpos }
  | id = Id; Lparen; args = exp_non_empty; Rparen
    { let (x, xs) = args in span (E_app (id, x :: xs)) $startpos $endpos }
  | id = Id; Lparen; Rparen
    { span (E_app (id, [])) $startpos $endpos }
  | v = Var
    { span (E_var v) $startpos $endpos }
  | s = String
    { span (E_string s) $startpos $endpos }
  | DotDot
    { span E_parent $startpos $endpos }
  | Lsquare; Rsquare
    { span (E_list []) $startpos $endpos }
  | Lsquare; es = exp_list; Rsquare
    { span (E_list es) $startpos $endpos }
  | Lparen; e = exp; Rparen
    { e }

dependency:
  | Requires; xs = exp_comma_block
    { D_requires xs }
  | After; xs = exp_comma_block
    { D_after xs }
  | Before; xs = exp_comma_block
    { D_before xs }
  | Default
    { D_default }
  | Optional
    { D_optional }

mdl_def:
  | d = dependency
    { span (M_dep d) $startpos $endpos }
  | m = mdl
    { span (M_module m) $startpos $endpos }
  | Directory; e = exp
    { span (M_directory e) $startpos $endpos }
  | Files; es = exp_comma_block
    { span (M_files es) $startpos $endpos }

mdl:
  | name = IdLcurly; defs = separated_list(Semi?, mdl_def); Rcurly
    { { name = span (fst name) $startpos(name) (snd name);
        defs;
        span = ($startpos, $endpos)
      } : mdl }

def:
  | Test; ids = nonempty_list(Id)
    { span (Def_test ids) $startpos $endpos }
  | Variable; id = Id; Eq; e = exp
    { span (Def_var (span id $startpos(id) $endpos(id), e)) $startpos $endpos }
  | m = mdl
    { span (Def_module m) $startpos $endpos }

file:
  | defs = list(def); Eof
    { defs }
