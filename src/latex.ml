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
open Printf

module StringSet = Set.Make(String);;

let opt_prefix = ref "sail"
let opt_directory = ref "sail_latex"
let opt_simple_val = ref true

let rec unique_postfix n =
  if n < 0 then
    ""
  else if n >= 26 then
    String.make 1 (Char.chr (n mod 26 + 65)) ^ unique_postfix (n - 26)
  else
    String.make 1 (Char.chr (n mod 26 + 65))

type latex_state =
  { mutable noindent : bool;
    mutable this : id option;
    mutable norefs : StringSet.t;
    mutable generated_names : string Bindings.t
  }

let reset_state state =
  state.noindent <- false;
  state.this <- None;
  state.norefs <- StringSet.empty;
  state.generated_names <- Bindings.empty

let state =
  { noindent = false;
    this = None;
    norefs = StringSet.empty;
    generated_names = Bindings.empty
  }

let rec unique_postfix n =
  if n < 0 then
    ""
  else if n >= 26 then
    String.make 1 (Char.chr (n mod 26 + 65)) ^ unique_postfix (n - 26)
  else
    String.make 1 (Char.chr (n mod 26 + 65))

type id_category =
  | Function
  | Val
  | Overload of int
  | FunclCtor of id * int
  | FunclNum of int
  | FunclApp of string
  | Type

let number_replacements =
    [ ("0", "Zero");
      ("1", "One");
      ("2", "Two");
      ("3", "Three");
      ("4", "Four");
      ("5", "Five");
      ("6", "Six");
      ("7", "Seven");
      ("8", "Eight");
      ("9", "Nine") ]

(* add to this as needed *)
let other_replacements =
    [ ("_", "Underscore") ]

let char_replace str replacements =
  List.fold_left (fun str (from, into) -> Str.global_replace (Str.regexp_string from) into str) str replacements

let replace_numbers str =
  char_replace str number_replacements

let replace_others str =
  char_replace str other_replacements

let category_name = function
  | Function -> "fn"
  | Val -> "val"
  | Type -> "type"
  | Overload n -> "overload" ^ unique_postfix n
  | FunclNum n -> "fcl" ^ unique_postfix n
  | FunclCtor (id, n) ->
     let str = replace_others (replace_numbers (Util.zencode_string (string_of_id id))) in
     "fcl" ^ String.sub str 1 (String.length str - 1) ^ unique_postfix n
  | FunclApp str -> "fcl" ^ str

let category_name_val = function
  | Val -> ""
  | cat -> category_name cat

let category_name_simple = function
  | Function -> "fn"
  | Val -> "val"
  | Type -> "type"
  | Overload n -> "overload"
  | FunclNum _ -> "fcl"
  | FunclCtor (_, _) -> "fcl"
  | FunclApp _ -> "fcl"

(* Generate a unique latex identifier from a Sail identifier. We store
   a mapping from identifiers to strings in state so we always return
   the same latex id for a sail id. *)
let latex_id id =
  if Bindings.mem id state.generated_names then
    Bindings.find id state.generated_names
  else
    let str = string_of_id id in
    let r = Str.regexp {|_\([a-zA-Z0-9]\)|} in
    let str =
      (* Convert to CamelCase. OCaml's regexp library is a bit arcane. *)
      let str = ref str in
      try
        while true do
          ignore (Str.search_forward r !str 0);
          let replace = (Str.matched_group 0 !str).[1] |> Char.uppercase_ascii |> String.make 1 in
          str := Str.replace_first r replace !str
        done; ""
      with Not_found -> !str
    in
    (* If we have any other weird symbols in the id, remove them using Util.zencode_string (removing the z prefix) *)
    let str = Util.zencode_string str in
    let str = String.sub str 1 (String.length str - 1) in
    (* Latex only allows letters in identifiers, so replace all numbers and other characters *)
    let str = replace_others (replace_numbers str) in

    let generated = state.generated_names |> Bindings.bindings |> List.map snd |> StringSet.of_list in

    (* The above makes maps different names to the same name, so we need
     to keep track of what names we've generated an ensure that they
     remain unique. *)
    let rec unique n str =
      if StringSet.mem (str ^ unique_postfix n) generated then
        unique (n + 1) str
      else
        str ^ unique_postfix n
    in
    let str = unique (-1) str in
    state.generated_names <- Bindings.add id str state.generated_names;
    str

let refcode_string str =
  Str.global_replace (Str.regexp "_") "zy" (Util.zencode_string str)

let refcode_id id = refcode_string (string_of_id id)

let inline_code str = sprintf "\\lstinline{%s}" str

let text_code str =
  str
  |> Str.global_replace (Str.regexp_string "_") "\\_"
  |> Str.global_replace (Str.regexp_string ">") "$<$"
  |> Str.global_replace (Str.regexp_string "<") "$>$"

let replace_this str =
  match state.this with
  | Some id ->
     str
     |> Str.global_replace (Str.regexp_string "NAME") (text_code (string_of_id id))
     |> Str.global_replace (Str.regexp_string "THIS") (inline_code (string_of_id id))
  | None -> str

let latex_of_markdown str =
  let open Omd in
  let open Printf in

  let rec format_elem = function
    | Paragraph elems ->
       let prepend = if state.noindent then (state.noindent <- false; "\\noindent ") else "" in
       prepend ^ format elems ^ "\n\n"
    | Text str -> Str.global_replace (Str.regexp_string "_") "\\_" str
    | Emph elems -> sprintf "\\emph{%s}" (format elems)
    | Bold elems -> sprintf "\\textbf{%s}" (format elems)
    | Ref (r, "THIS", alt, _) ->
       begin match state.this with
       | Some id -> sprintf "\\hyperref[%s]{%s}" (refcode_string (string_of_id id)) (replace_this alt)
       | None -> failwith "Cannot create link to THIS"
       end
    | Ref (r, name, alt, _) ->
       (* special case for [id] (format as code) *)
       let format_fn = if name = alt then inline_code else replace_this in
       begin match r#get_ref name with
       | None -> sprintf "\\hyperref[%s]{%s}" (refcode_string name) (format_fn alt)
       | Some (link, _) -> sprintf "\\hyperref[%s]{%s}" (refcode_string link) (format_fn alt)
       end
    | Url (href, text, "") ->
       sprintf "\\href{%s}{%s}" href (format text)
    | Url (href, text, reference) ->
       sprintf "%s\\footnote{%s~\\url{%s}}" (format text) reference href
    | Code (_, code) ->
       sprintf "\\lstinline`%s`" code
    | Code_block (lang, code) ->
       let lang = if lang = "" then "sail" else lang in
       let uid = Digest.string str |> Digest.to_hex in
       let chan = open_out (Filename.concat !opt_directory (sprintf "block%s.%s" uid lang)) in
       output_string chan code;
       close_out chan;
       sprintf "\\lstinputlisting[language=%s]{%s/block%s.%s}" lang !opt_directory uid lang
    | Ul list ->
       "\\begin{itemize}\n\\item "
       ^ Util.string_of_list "\n\\item " format list
       ^ "\n\\end{itemize}"
    | Br -> "\n"
    | NL -> "\n"
    | elem -> failwith ("Can't convert to latex: " ^ to_text [elem])

  and format elems =
    String.concat "" (List.map format_elem elems)
  in

  replace_this (format (of_string str))

let docstring = function
  | Parse_ast.Documented (str, _) -> string (latex_of_markdown str)
  | _ -> empty

let add_links str =
  let r = Str.regexp {|\([a-zA-Z0-9_]+\)\([ ]*\)(|} in
  let subst s =
    let keywords = StringSet.of_list
      [ "function"; "forall"; "if"; "then"; "else"; "exit"; "return"; "match"; "vector";
        "assert"; "constraint"; "let"; "in"; "atom"; "range"; "throw"; "sizeof"; "foreach" ]
    in
    let fn = Str.matched_group 1 s in
    let spacing = Str.matched_group 2 s in
    if StringSet.mem fn keywords || StringSet.mem fn state.norefs then
      fn ^ spacing ^ "("
    else
      Printf.sprintf "#\\hyperref[%s]{%s}#%s(" (refcode_string fn) (Str.global_replace (Str.regexp "_") {|\_|} fn) spacing
  in
  Str.global_substitute r subst str

let latex_loc no_loc l =
  match l with
  | Parse_ast.Range (_, _) | Parse_ast.Documented (_, Parse_ast.Range (_, _)) ->
     begin
       let using_color = !Util.opt_colors in
       Util.opt_colors := false;
       let code = Util.split_on_char '\n' (Reporting.loc_to_string l) in
       let doc = match code with
         | _ :: _ :: code -> string (add_links (String.concat "\n" code))
         | _ -> empty
       in
       Util.opt_colors := using_color;
       doc ^^ hardline
     end

  | _ -> docstring l ^^ no_loc

let commands = ref StringSet.empty

let doc_spec_simple (VS_aux (VS_val_spec (ts, id, ext, is_cast), _)) =
  Pretty_print_sail.doc_id id ^^ space
  ^^ colon ^^ space
  ^^ Pretty_print_sail.doc_typschm ~simple:true ts

let rec latex_command cat id no_loc ((l, _) as annot) =
  state.this <- Some id;
  let labelling = match cat with
    | Val -> sprintf "\\label{%s}" (refcode_id id)
    | _ -> sprintf "\\label{%s%s}" (category_name cat) (refcode_id id)
  in
  (* To avoid problems with verbatim environments in commands, we have
     to put the sail code for each command in a separate file. *)
  let code_file = category_name cat ^ Util.file_encode_string (string_of_id id) ^ ".tex" in
  let chan = open_out (Filename.concat !opt_directory code_file) in
  let doc = if cat = Val then no_loc else latex_loc no_loc l in
  output_string chan (Pretty_print_sail.to_string doc);
  close_out chan;

  ksprintf string "\\newcommand{\\%s%s%s}{\\phantomsection%s\\saildoc%s{" !opt_prefix (category_name cat) (latex_id id) labelling (category_name_simple cat)
  ^^ docstring l ^^ string "}{"
  ^^ ksprintf string "\\lstinputlisting[language=sail]{%s}}}" (Filename.concat !opt_directory code_file)

let latex_label str id =
  string (Printf.sprintf "\\label{%s:%s}" str (Util.zencode_string (string_of_id id)))

let counter = ref 0

let rec app_code (E_aux (exp, _)) =
  match exp with
  | E_app (f, [exp]) when Id.compare f (mk_id "Some") = 0 -> app_code exp
  | E_app (f, [exp]) -> latex_id f ^ app_code exp
  | E_app (f, _) -> latex_id f
  | E_id id -> latex_id id
  | _ -> ""

let latex_funcls def =
  let module StringMap = Map.Make(String) in
  let counter = ref 0 in
  let app_codes = ref StringMap.empty in
  let ctors = ref Bindings.empty in

  let rec latex_funcls' def =
    let counter = ref (-1) in
    let next funcls = twice hardline ^^ latex_funcls' def funcls in
    let funcl_command (FCL_Funcl (id, pexp)) =
      match pexp with
      | Pat_aux (Pat_exp (P_aux (P_app (ctor, _), _), _), _) ->
         let n = try Bindings.find ctor !ctors with Not_found -> -1 in
         ctors := Bindings.add ctor (n + 1) !ctors;
         FunclCtor (ctor, n), id
      | Pat_aux (Pat_exp (_, exp), _) ->
         let ac = app_code exp in
         let n = try StringMap.find ac !app_codes with Not_found -> -1 in
         app_codes := StringMap.add ac (n + 1) !app_codes;
         FunclApp (ac ^ unique_postfix n), id
      | _ -> incr counter; (FunclNum (!counter + 64), id)
    in
    function
    | (FCL_aux (funcl_aux, annot) as funcl) :: funcls ->
       let cat, id = funcl_command funcl_aux in
       let first = latex_command cat id (Pretty_print_sail.doc_funcl funcl) annot in
       first ^^ next funcls
    | [] -> empty
  in
  latex_funcls' def

let process_pragma l command =
  let n = try String.index command ' ' with Not_found -> String.length command in
  let cmd = Str.string_before command n in
  let arg = String.trim (Str.string_after command n) in

  match cmd with
  | "noindent" ->
     state.noindent <- true;
     None

  | "noref" ->
     state.norefs <- StringSet.add arg state.norefs;
     None

  | "newcommand" ->
     let n = try String.index arg ' ' with Not_found -> failwith "No command given" in
     let name = Str.string_before arg n in
     let body = String.trim (latex_of_markdown (Str.string_after arg n)) in
     Some (ksprintf string "\\newcommand{\\%s}{%s}" name body)

  | _ ->
     Util.warn (Printf.sprintf "Bad latex pragma %s" (Reporting.loc_to_string l));
     None

let tdef_id = function
  | TD_abbrev (id, _, _) -> id
  | TD_record (id, _, _, _, _) -> id
  | TD_variant (id, _, _, _, _) -> id
  | TD_enum (id, _, _, _) -> id
  | TD_bitfield (id, _, _) -> id

let defs (Defs defs) =
  reset_state state;

  let overload_counter = ref 0 in

  let valspecs = ref IdSet.empty in
  let fundefs = ref IdSet.empty in
  let typedefs = ref IdSet.empty in

  let latex_def def =
    match def with
    | DEF_overload (id, ids) ->
       let doc =
         string (Printf.sprintf "overload %s = {%s}" (string_of_id id) (Util.string_of_list ", " string_of_id ids))
       in
       incr overload_counter;
       Some (latex_command (Overload !overload_counter) id doc (id_loc id, None))

    | DEF_spec (VS_aux (VS_val_spec (_, id, _, _), annot) as vs) as def ->
       valspecs := IdSet.add id !valspecs;
       if !opt_simple_val then
         Some (latex_command Val id (doc_spec_simple vs) annot)
       else
         Some (latex_command Val id (Pretty_print_sail.doc_spec ~comment:false vs) annot)

    | DEF_fundef (FD_aux (FD_function (_, _, _, [FCL_aux (FCL_Funcl (id, _), _)]), annot)) as def ->
       fundefs := IdSet.add id !fundefs;
       Some (latex_command Function id (Pretty_print_sail.doc_def def) annot)

    | DEF_type (TD_aux (tdef, annot)) as def ->
       let id = tdef_id tdef in
       typedefs := IdSet.add id !typedefs;
       Some (latex_command Type id (Pretty_print_sail.doc_def def) annot)

    | DEF_fundef (FD_aux (FD_function (_, _, _, funcls), annot)) as def ->
       Some (latex_funcls def funcls)

    | DEF_pragma ("latex", command, l) ->
       process_pragma l command

    | _ -> None
  in

  let rec process_defs = function
    | [] -> empty
    | def :: defs ->
       let tex = match latex_def def with
         | Some tex -> tex ^^ twice hardline
         | None -> empty
       in
       tex ^^ process_defs defs
  in

  let tex = process_defs defs in

  (* Rather than having latex functions that use mangled names, like
     \sailfnmyFunction for a function my_function, we can write
     \sailfn{my_function} by generating a latex macro that compares
     identifiers then outputs the correct mangled command. *)
  let id_command cat ids =
    sprintf "\\newcommand{\\%s%s}[1]{\n  " !opt_prefix (category_name cat)
    ^ Util.string_of_list "%\n  " (fun id -> sprintf "\\ifstrequal{#1}{%s}{\\%s%s%s}{}" (string_of_id id) !opt_prefix (category_name cat) (latex_id id))
                          (IdSet.elements ids)
    ^ "}"
    |> string
  in
  let ref_command cat ids =
    sprintf "\\newcommand{\\%sref%s}[2]{\n  " !opt_prefix (category_name cat)
    ^ Util.string_of_list "%\n  " (fun id -> sprintf "\\ifstrequal{#1}{%s}{\\hyperref[%s%s]{#2}}{}" (string_of_id id) (category_name_val cat) (refcode_id id))
                          (IdSet.elements ids)
    ^ "}"
    |> string
  in

  tex
  ^^ separate (twice hardline) [id_command Val !valspecs;
                                ref_command Val !valspecs;
                                id_command Function !fundefs;
                                ref_command Function !fundefs;
                                id_command Type !typedefs;
                                ref_command Type !typedefs]
  ^^ hardline
