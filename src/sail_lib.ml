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

(** A Sail library *)

(* This library is not well-thought. It has grown driven by the need to
 * reuse some components of Sail in the Power XML extraction tool. It
 * should by no means by considered stable (hence the lack of mli
 * interface file), and is not intended for general consumption. Use at
 * your own risks. *)

module Pretty = Pretty_print

let parse_exps s =
  let lexbuf = Lexing.from_string s in
  try
  let pre_exps = Parser.nonempty_exp_list Lexer.token lexbuf in
  List.map (Initial_check.to_ast_exp Type_internal.initial_kind_env (Ast.Ord_aux(Ast.Ord_inc,Parse_ast.Unknown))) pre_exps
  with
    | Parsing.Parse_error ->
        let pos = Lexing.lexeme_start_p lexbuf in
        let msg = Printf.sprintf "syntax error on character %d" pos.Lexing.pos_cnum in
        failwith msg
    | Parse_ast.Parse_error_locn(l,m) ->
        let rec format l = match l with
        | Parse_ast.Unknown -> "???"
        | Parse_ast.Range(p1,p2) -> Printf.sprintf "%d:%d" p1.Lexing.pos_cnum p2.Lexing.pos_cnum
        | Parse_ast.Generated l -> Printf.sprintf "code generated near: %s" (format l)
        | Parse_ast.Int(s,_) -> Printf.sprintf "code for by: %s" s in
        let msg = Printf.sprintf "syntax error: %s %s" (format l) m in
        failwith msg
    | Lexer.LexError(s,p) ->
        let msg = Printf.sprintf "lexing error: %s %d" s p.Lexing.pos_cnum in
        failwith msg
        


