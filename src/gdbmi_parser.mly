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

open Gdbmi_types

%}

%token Eof
%token Eq Lsquare Rsquare Lcurly Rcurly Comma Caret
%token <string> String Id
%token <int> Num

%start response_eof
%type <Gdbmi_types.response> response_eof

%%

map_elem:
  | Id Eq output
    { ($1, $3) }

output:
  | String
    { String $1 }
  | Lsquare separated_list(Comma, output) Rsquare
    { Seq $2 }
  | Lcurly separated_list(Comma, map_elem) Rcurly
    { Assoc $2 }

response:
  | Num Caret Id Comma separated_list(Comma, map_elem)
    { Result ($1, $3, $5) }

response_eof:
  | response Eof
    { $1 }