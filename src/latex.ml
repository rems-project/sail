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

let opt_prefix_latex = ref "sail"

let replace_numbers str =
  str
  |> Str.global_replace (Str.regexp "0") "zero"
  |> Str.global_replace (Str.regexp "1") "one"
  |> Str.global_replace (Str.regexp "2") "two"
  |> Str.global_replace (Str.regexp "3") "three"
  |> Str.global_replace (Str.regexp "4") "four"
  |> Str.global_replace (Str.regexp "5") "five"
  |> Str.global_replace (Str.regexp "6") "six"
  |> Str.global_replace (Str.regexp "7") "seven"
  |> Str.global_replace (Str.regexp "8") "eight"
  |> Str.global_replace (Str.regexp "9") "nine"

let namecode_string str =
  let str = Str.global_replace (Str.regexp "_") "" (Util.zencode_string str) in
  replace_numbers (String.sub str 1 (String.length str - 1))

let namecode_id id = namecode_string (string_of_id id)

let refcode_string str =
  replace_numbers (Str.global_replace (Str.regexp "_") "zy" (Util.zencode_string str))

let refcode_id id = refcode_string (string_of_id id)

let docstring = function
  | Parse_ast.Documented (str, _) -> string str
  | _ -> empty

let add_links str =
  let r = Str.regexp {|\([a-zA-Z0-9_]+\)\([ ]*\)(|} in
  let subst s =
    let module StringSet = Set.Make(String) in
    let keywords = StringSet.of_list
      [ "function"; "forall"; "if"; "then"; "else"; "exit"; "return"; "match"; "vector";
        "assert"; "constraint"; "let"; "in"; "atom"; "range"; "throw"; "sizeof"; "foreach" ]
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

module StringSet = Set.Make(String)

let commands = ref StringSet.empty

let rec latex_command ?prefix:(prefix="") ?label:(label=None) dir cmd no_loc ((l, _) as annot) =
  let labelling = match label with
    | None -> ""
    | Some l -> Printf.sprintf "\\label{%s}" l
  in
  let cmd = !opt_prefix_latex ^ prefix ^ cmd in
  let lcmd = String.lowercase cmd in  (* lowercase to avoid file names differing only by case *)
  if StringSet.mem lcmd !commands then
    latex_command ~label:label dir (cmd ^ "v") no_loc annot
  else
    begin
      commands := StringSet.add lcmd !commands;
      let oc = open_out (Filename.concat dir (cmd ^ ".tex")) in
      output_string oc (Pretty_print_sail.to_string (latex_loc no_loc l));
      close_out oc;
      string (Printf.sprintf "\\newcommand{\\%s}{%s " cmd labelling) ^^ (docstring l) ^^ string (Printf.sprintf "\\lstinputlisting[language=sail]{%s/%s.tex}}" dir cmd)
    end

let latex_command_id ?prefix:(prefix="") dir id no_loc annot =
  latex_command ~prefix:prefix ~label:(Some (refcode_id id)) dir (namecode_id id) no_loc annot

let latex_label str id =
  string (Printf.sprintf "\\label{%s:%s}" str (Util.zencode_string (string_of_id id)))

let counter = ref 0

let rec app_code (E_aux (exp, _)) =
  match exp with
  | E_app (f, [exp]) -> namecode_id f ^ app_code exp
  | E_app (f, _) -> namecode_id f
  | E_id id -> namecode_id id
  | _ -> ""

let rec latex_funcls dir def =
  let next funcls = twice hardline ^^ latex_funcls dir def funcls in
  let funcl_command (FCL_Funcl (id, pexp)) =
    match pexp with
    | Pat_aux (Pat_exp (P_aux (P_app (ctor, _), _), _), _) -> namecode_id id ^ namecode_id ctor
    | Pat_aux (Pat_exp (_, exp), _) -> namecode_id id ^ app_code exp
    | _ -> (incr counter; namecode_id id ^ String.make 1 (Char.chr (!counter + 64)))
  in
  function
  | (FCL_aux (funcl_aux, annot) as funcl) :: funcls ->
     let first = latex_command ~prefix:"fn" dir (funcl_command funcl_aux) (Pretty_print_sail.doc_funcl funcl) annot in
     first ^^ next funcls
  | [] -> empty

let rec latex_defs dir (Defs defs) =
  let next defs = twice hardline ^^ latex_defs dir (Defs defs) in
  match defs with
  | DEF_overload (id, ids) :: defs ->
     let doc =
       string (Printf.sprintf "overload %s = {%s}" (string_of_id id) (Util.string_of_list ", " string_of_id ids))
     in
     latex_command_id dir id doc (Parse_ast.Unknown, None)
     ^^ next defs
  | (DEF_type (TD_aux (TD_abbrev (id, _, _), annot)) as def) :: defs ->
     latex_command_id dir id (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_type (TD_aux (TD_record (id, _, _, _, _), annot)) as def) :: defs ->
     latex_command_id dir id (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_type (TD_aux (TD_enum (id, _, _, _), annot)) as def) :: defs ->
     latex_command_id dir id (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_spec (VS_aux (VS_val_spec (_, id, _, _), annot)) as def) :: defs ->
     latex_command_id dir id (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, _), _)]), annot)) as def) :: defs ->
     latex_command_id dir ~prefix:"fn" id (Pretty_print_sail.doc_def def) annot ^^ next defs
  | (DEF_fundef (FD_aux (FD_function (_, _, _, funcls), annot)) as def) :: defs -> latex_funcls dir def funcls ^^ next defs
  | _ :: defs -> latex_defs dir (Defs defs)
  | [] -> empty
