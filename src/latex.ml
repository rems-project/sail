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

open Ast
open Ast_util
open PPrint

let docstring = function
  | Parse_ast.Documented (str, _) -> string str
  | _ -> empty

let latex_loc no_loc l =
  match l with
  | Parse_ast.Range (_, _) | Parse_ast.Documented (_, Parse_ast.Range (_, _)) ->
     begin
       let using_color = !Util.opt_colors in
       Util.opt_colors := false;
       let code = Util.split_on_char '\n' (Reporting_basic.loc_to_string l) in
       let doc = match code with
         | _ :: _ :: code -> string (String.concat "\n" code)
         | _ -> empty
       in
       Util.opt_colors := using_color;
       doc ^^ hardline
     end

  | _ -> docstring l ^^ no_loc

let latex_code no_loc ((l, _) as annot) =
  docstring l
  ^^ string "\\begin{lstlisting}" ^^ hardline
  ^^ latex_loc no_loc l
  ^^ string "\\end{lstlisting}"

let rec latex_funcls def =
  let next funcls = twice hardline ^^ latex_funcls def funcls in
  function
  | (FCL_aux (_, annot) as funcl) :: funcls ->
     latex_code (Pretty_print_sail.doc_funcl funcl) annot ^^ next funcls
  | [] -> empty

let rec latex_defs (Defs defs) =
  let next defs = twice hardline ^^ latex_defs (Defs defs) in
  match defs with
  | (DEF_spec (VS_aux (_, annot)) as def) :: defs ->
     latex_code (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, [_]), annot)) as def) :: defs ->
     latex_code (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, funcls), annot)) as def) :: defs -> latex_funcls def funcls ^^ next defs
  | _ :: defs -> latex_defs (Defs defs)
  | [] -> empty
