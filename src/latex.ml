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

let refcode_string str =
  Str.global_replace (Str.regexp "_") "zy" (Util.zencode_string str)

let refcode_id id = refcode_string (string_of_id id)

let docstring = function
  | Parse_ast.Documented (str, _) -> string str
  | _ -> empty

let add_links str =
  let r = Str.regexp {|\([a-zA-Z0-9_]+\)\([ ]*\)(|} in
  let subst s =
    let module StringSet = Set.Make(String) in
    let keywords = StringSet.of_list
      [ "function"; "forall"; "if"; "then"; "else"; "exit"; "return"; "match";
        "assert"; "constraint"; "let"; "in"; "atom"; "range"; "throw" ]
    in
    let fn = Str.matched_group 1 s in
    let spacing = Str.matched_group 2 s in
    if StringSet.mem fn keywords then
      fn ^ spacing ^ "("
    else
      Printf.sprintf {|#\hyperref[%s]{%s}#%s(|} (refcode_string fn) (Str.global_replace (Str.regexp "_") {|\_|} fn) spacing
  in
  Str.global_substitute r subst str

let latex_loc no_loc l =
  match l with
  | Parse_ast.Range (_, _) | Parse_ast.Documented (_, Parse_ast.Range (_, _)) ->
     begin
       let using_color = !Util.opt_colors in
       Util.opt_colors := false;
       let code = Util.split_on_char '\n' (Reporting_basic.loc_to_string l) in
       let doc = match code with
         | _ :: _ :: code -> string (add_links (String.concat "\n" code))
         | _ -> empty
       in
       Util.opt_colors := using_color;
       doc ^^ hardline
     end

  | _ -> docstring l ^^ no_loc

let latex_code ?label:(label=None) no_loc ((l, _) as annot) =
  let open_listing = match label with
    | None -> "\\begin{lstlisting}"
    | Some l -> Printf.sprintf "\\begin{lstlisting}[label={%s}]" l
  in
  docstring l
  ^^ string open_listing ^^ hardline
  ^^ latex_loc no_loc l
  ^^ string "\\end{lstlisting}"

let latex_label str id =
  string (Printf.sprintf "\\label{%s:%s}" str (Util.zencode_string (string_of_id id)))

let rec latex_funcls def =
  let next funcls = twice hardline ^^ latex_funcls def funcls in
  function
  | (FCL_aux (_, annot) as funcl) :: funcls ->
     latex_code (Pretty_print_sail.doc_funcl funcl) annot ^^ next funcls
  | [] -> empty

let rec latex_defs (Defs defs) =
  let next defs = twice hardline ^^ latex_defs (Defs defs) in
  match defs with
  | DEF_overload (id, ids) :: defs ->
     string (Printf.sprintf {|\begin{lstlisting}[label={%s}]|} (refcode_id id)) ^^ hardline
     ^^ string (Printf.sprintf "overload %s = {%s}" (string_of_id id) (Util.string_of_list ", " string_of_id ids))
     ^^ string {|\end{lstlisting}|}
     ^^ next defs
  | (DEF_type (TD_aux (TD_abbrev (id, _, _), annot)) as def) :: defs ->
     latex_code ~label:(Some (refcode_id id)) (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_type (TD_aux (TD_record (id, _, _, _, _), annot)) as def) :: defs ->
     latex_code ~label:(Some (refcode_id id)) (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_type (TD_aux (TD_enum (id, _, _, _), annot)) as def) :: defs ->
     latex_code ~label:(Some (refcode_id id)) (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_spec (VS_aux (VS_val_spec (_, id, _, _), annot)) as def) :: defs ->
     latex_code ~label:(Some (refcode_id id)) (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, [_]), annot)) as def) :: defs ->
     latex_code (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, funcls), annot)) as def) :: defs -> latex_funcls def funcls ^^ next defs
  | _ :: defs -> latex_defs (Defs defs)
  | [] -> empty
