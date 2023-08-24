(****************************************************************************)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(****************************************************************************)

open Libsail

open Ast
open Ast_defs
open Ast_util
open PPrint
open Printf

module StringSet = Set.Make (String)

let opt_prefix = ref "sail"
let opt_directory = ref "sail_latex"
let opt_simple_val = ref true
let opt_abbrevs = ref ["e.g."; "i.e."]

let rec unique_postfix n =
  if n < 0 then ""
  else if n >= 26 then String.make 1 (Char.chr ((n mod 26) + 65)) ^ unique_postfix (n - 26)
  else String.make 1 (Char.chr ((n mod 26) + 65))

type latex_state = {
  mutable noindent : bool;
  mutable this : id option;
  mutable norefs : StringSet.t;
  mutable generated_names : string Bindings.t;
  mutable commands : StringSet.t;
}

let reset_state state =
  state.noindent <- false;
  state.this <- None;
  state.norefs <- StringSet.empty;
  state.generated_names <- Bindings.empty;
  state.commands <- StringSet.empty

let state =
  {
    noindent = false;
    this = None;
    norefs = StringSet.empty;
    generated_names = Bindings.empty;
    commands = StringSet.empty;
  }

let rec unique_postfix n =
  if n < 0 then ""
  else if n >= 26 then String.make 1 (Char.chr ((n mod 26) + 65)) ^ unique_postfix (n - 26)
  else String.make 1 (Char.chr ((n mod 26) + 65))

type id_category =
  | Function
  | Val
  | Overload of int
  | FunclCtor of id * int
  | FunclNum of int
  | FunclApp of string
  | Type
  | Let
  | Register
  | Outcome

let number_replacements =
  [
    ("0", "Zero");
    ("1", "One");
    ("2", "Two");
    ("3", "Three");
    ("4", "Four");
    ("5", "Five");
    ("6", "Six");
    ("7", "Seven");
    ("8", "Eight");
    ("9", "Nine");
  ]

(* add to this as needed *)
let other_replacements = [("_", "Underscore")]

let char_replace str replacements =
  List.fold_left (fun str (from, into) -> Str.global_replace (Str.regexp_string from) into str) str replacements

let replace_numbers str = char_replace str number_replacements

let replace_others str = char_replace str other_replacements

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
  | Let -> "let"
  | Register -> "register"
  | Outcome -> "outcome"

let category_name_val = function Val -> "" | cat -> category_name cat

let category_name_simple = function
  | Function -> "fn"
  | Val -> "val"
  | Type -> "type"
  | Overload n -> "overload"
  | FunclNum _ -> "fcl"
  | FunclCtor (_, _) -> "fcl"
  | FunclApp _ -> "fcl"
  | Let -> "let"
  | Register -> "register"
  | Outcome -> "outcome"

(* Generate a unique latex identifier from a Sail identifier. We store
   a mapping from identifiers to strings in state so we always return
   the same latex id for a sail id. *)
let latex_id_raw id =
  if Bindings.mem id state.generated_names then Bindings.find id state.generated_names
  else (
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
        done;
        ""
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
      if StringSet.mem (str ^ unique_postfix n) generated then unique (n + 1) str else str ^ unique_postfix n
    in
    let str = unique (-1) str in
    state.generated_names <- Bindings.add id str state.generated_names;
    str
  )

let latex_cat_id cat id = !opt_prefix ^ category_name cat ^ latex_id_raw id

let rec app_code (E_aux (exp, _)) =
  match exp with
  | E_app (f, [exp]) when Id.compare f (mk_id "Some") = 0 -> app_code exp
  | E_app (f, [exp]) -> latex_id_raw f ^ app_code exp
  | E_app (f, _) -> latex_id_raw f
  | E_id id -> latex_id_raw id
  | _ -> ""

let refcode_cat_string cat str =
  let refcode_str = Str.global_replace (Str.regexp "_") "zy" (Util.zencode_string str) in
  !opt_prefix ^ category_name_val cat ^ refcode_str

let refcode_cat_id prefix id = refcode_cat_string prefix (string_of_id id)

let refcode_id = refcode_cat_id Val

let refcode_string = refcode_cat_string Val

let inline_code str = sprintf "\\lstinline{%s}" str

let guard_abbrevs str =
  let frags = List.map Str.quote !opt_abbrevs in
  let alternation = String.concat "\\|" frags in
  let regex = Str.regexp ("\\b\\(" ^ alternation ^ "\\)\\( \\|$\\)") in
  (* We use this seemingly-unnecessary wrapper so consumers like
     cheri-architecture that want to use \xpatch on our output don't run into
     issues like https://tex.stackexchange.com/q/565659/175942. *)
  Str.global_replace regex "\\saildocabbrev{\\1}\\2" str

let text_code str =
  str |> guard_abbrevs
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
        let prepend =
          if state.noindent then (
            state.noindent <- false;
            "\\noindent "
          )
          else ""
        in
        prepend ^ format elems ^ "\n\n"
    | Text str -> text_code str
    | Emph elems -> sprintf "\\emph{%s}" (format elems)
    | Bold elems -> sprintf "\\textbf{%s}" (format elems)
    | Ref (r, "THIS", alt, _) -> begin
        match state.this with
        | Some id -> sprintf "\\hyperref[%s]{%s}" (refcode_id id) (replace_this alt)
        | None -> failwith "Cannot create link to THIS"
      end
    | Ref (r, name, alt, _) ->
        (* special case for [id] (format as code) *)
        let format_fn = if name = alt then inline_code else replace_this in
        (* Do not attempt to escape link destinations wrapped in <> *)
        if Str.string_match (Str.regexp "<.+>") name 0 then
          sprintf "\\hyperref[%s]{%s}" (String.sub name 1 (String.length name - 2)) (format_fn alt)
        else begin
          match r#get_ref name with
          | None -> sprintf "\\hyperref[%s]{%s}" (refcode_string name) (format_fn alt)
          | Some (link, _) -> sprintf "\\hyperref[%s]{%s}" (refcode_string link) (format_fn alt)
        end
    | Url (href, text, "") -> sprintf "\\href{%s}{%s}" href (format text)
    | Url (href, text, reference) -> sprintf "%s\\footnote{%s~\\url{%s}}" (format text) reference href
    | Code (_, code) -> sprintf "\\lstinline`%s`" code
    | Code_block (lang, code) ->
        let lang = if lang = "" then "sail" else lang in
        let uid = Digest.string str |> Digest.to_hex in
        let chan = open_out (Filename.concat !opt_directory (sprintf "block%s.%s" uid lang)) in
        output_string chan code;
        close_out chan;
        sprintf "\\lstinputlisting[language=%s]{%s/block%s.%s}" lang !opt_directory uid lang
    | Ul list | Ulp list ->
        "\\begin{itemize}\n\\item " ^ Util.string_of_list "\n\\item " format list ^ "\n\\end{itemize}\n"
    | Ol list | Olp list ->
        "\\begin{enumerate}\n\\item " ^ Util.string_of_list "\n\\item " format list ^ "\n\\end{enumerate}\n"
    | H1 header -> "\\section*{" ^ format header ^ "}\n"
    | H2 header -> "\\subsection*{" ^ format header ^ "}\n"
    | H3 header -> "\\subsubsection*{" ^ format header ^ "}\n"
    | H4 header -> "\\paragraph*{" ^ format header ^ "}\n"
    | Br -> "\n"
    | NL -> "\n"
    | elem -> failwith ("Can't convert to latex: " ^ Omd_backend.sexpr_of_md [elem])
  and format elems = String.concat "" (List.map format_elem elems) in

  replace_this (format (of_string str))

let docstring _ = empty

let add_links str =
  let r = Str.regexp {|\([a-zA-Z0-9_]+\)\([ ]*\)(|} in
  let subst s =
    let keywords =
      StringSet.of_list
        [
          "function";
          "forall";
          "if";
          "then";
          "else";
          "exit";
          "return";
          "match";
          "vector";
          "assert";
          "constraint";
          "let";
          "in";
          "atom";
          "range";
          "throw";
          "sizeof";
          "foreach";
        ]
    in
    let fn = Str.matched_group 1 s in
    let spacing = Str.matched_group 2 s in
    if StringSet.mem fn keywords || StringSet.mem fn state.norefs then fn ^ spacing ^ "("
    else
      Printf.sprintf "#\\hyperref[%s]{%s}#%s(" (refcode_string fn)
        (Str.global_replace (Str.regexp "_") {|\_|} fn)
        spacing
  in
  Str.global_substitute r subst str

let rec skip_lines in_chan = function
  | n when n <= 0 -> ()
  | n ->
      ignore (input_line in_chan);
      skip_lines in_chan (n - 1)

let rec read_lines in_chan = function
  | n when n <= 0 -> []
  | n ->
      let l = input_line in_chan in
      let ls = read_lines in_chan (n - 1) in
      l :: ls

let latex_loc no_loc l =
  match Reporting.simp_loc l with
  | Some (p1, p2) -> begin
      let open Lexing in
      try
        let in_chan = open_in p1.pos_fname in
        try
          skip_lines in_chan (p1.pos_lnum - 3);
          let code = read_lines in_chan (p2.pos_lnum - p1.pos_lnum + 3) in
          close_in in_chan;
          let doc = match code with _ :: _ :: code -> string (add_links (String.concat "\n" code)) | _ -> empty in
          doc ^^ hardline
        with _ ->
          close_in_noerr in_chan;
          docstring l ^^ no_loc
      with _ -> docstring l ^^ no_loc
    end
  | None -> docstring l ^^ no_loc

let doc_spec_simple (VS_aux (VS_val_spec (ts, id, ext), _)) =
  Pretty_print_sail.doc_id id ^^ space ^^ colon ^^ space ^^ Pretty_print_sail.doc_typschm ~simple:true ts

let latex_command cat id no_loc l =
  state.this <- Some id;
  (* To avoid problems with verbatim environments in commands, we have
     to put the sail code for each command in a separate file. *)
  let code_file = category_name cat ^ Util.file_encode_string (string_of_id id) ^ ".tex" in
  let chan = open_out (Filename.concat !opt_directory code_file) in
  let doc = if cat = Val then no_loc else latex_loc no_loc l in
  output_string chan (Pretty_print_sail.to_string doc);
  close_out chan;
  let command = sprintf "\\%s" (latex_cat_id cat id) in
  if StringSet.mem command state.commands then (
    Reporting.warn "" l ("Multiple instances of " ^ string_of_id id ^ " only generating latex for the first");
    empty
  )
  else begin
    state.commands <- StringSet.add command state.commands;

    ksprintf string "\\newcommand{%s}{\\saildoclabelled{%s}{\\saildoc%s{" command (refcode_cat_id cat id)
      (category_name_simple cat)
    ^^ docstring l ^^ string "}{"
    ^^ ksprintf string "\\lstinputlisting[language=sail]{%s}}}}" (Filename.concat !opt_directory code_file)
  end

let latex_funcls def =
  let module StringMap = Map.Make (String) in
  let counter = ref 0 in
  let app_codes = ref StringMap.empty in
  let ctors = ref Bindings.empty in

  let rec latex_funcls' def =
    let counter = ref (-1) in
    let next funcls = twice hardline ^^ latex_funcls' def funcls in
    let funcl_command (FCL_funcl (id, pexp)) =
      match pexp with
      | Pat_aux (Pat_exp (P_aux (P_app (ctor, _), _), _), _) ->
          let n = try Bindings.find ctor !ctors with Not_found -> -1 in
          ctors := Bindings.add ctor (n + 1) !ctors;
          (FunclCtor (ctor, n), id)
      | Pat_aux (Pat_exp (_, exp), _) ->
          let ac = app_code exp in
          let n = try StringMap.find ac !app_codes with Not_found -> -1 in
          app_codes := StringMap.add ac (n + 1) !app_codes;
          (FunclApp (ac ^ unique_postfix n), id)
      | _ ->
          incr counter;
          (FunclNum (!counter + 64), id)
    in
    function
    | (FCL_aux (funcl_aux, annot) as funcl) :: funcls ->
        let cat, id = funcl_command funcl_aux in
        let first = latex_command cat id (Pretty_print_sail.doc_funcl funcl) (fst annot).loc in
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
      Reporting.warn "Bad latex pragma at" l "";
      None

let tdef_id = function
  | TD_abbrev (id, _, _) -> id
  | TD_record (id, _, _, _) -> id
  | TD_variant (id, _, _, _) -> id
  | TD_enum (id, _, _) -> id
  | TD_bitfield (id, _, _) -> id

let defs { defs; _ } =
  reset_state state;

  let preamble =
    string
      ("\\providecommand\\saildoclabelled[2]{\\phantomsection\\label{#1}#2}\n"
     ^ "\\providecommand\\saildocval[2]{#1 #2}\n" ^ "\\providecommand\\saildocoutcome[2]{#1 #2}\n"
     ^ "\\providecommand\\saildocfcl[2]{#1 #2}\n" ^ "\\providecommand\\saildoctype[2]{#1 #2}\n"
     ^ "\\providecommand\\saildocfn[2]{#1 #2}\n" ^ "\\providecommand\\saildocoverload[2]{#1 #2}\n"
     ^ "\\providecommand\\saildocabbrev[1]{#1\\@}\n" ^ "\\providecommand\\saildoclet[2]{#1 #2}\n"
     ^ "\\providecommand\\saildocregister[2]{#1 #2}\n\n"
      )
  in

  let overload_counters = ref Bindings.empty in

  (* These map each id to the canonical id used for the LaTeX macro; usually the
     identity, but let bindings can produce multiple entries. *)
  let valspecs = ref Bindings.empty in
  let fundefs = ref Bindings.empty in
  let typedefs = ref Bindings.empty in
  let letdefs = ref Bindings.empty in
  let regdefs = ref Bindings.empty in
  let outcomedefs = ref Bindings.empty in

  let latex_def (DEF_aux (aux, _) as def) =
    match aux with
    | DEF_overload (id, ids) ->
        let doc =
          string (Printf.sprintf "overload %s = {%s}" (string_of_id id) (Util.string_of_list ", " string_of_id ids))
        in
        overload_counters := Bindings.update id (function None -> Some 0 | Some n -> Some (n + 1)) !overload_counters;
        let count = Bindings.find id !overload_counters in
        Some (latex_command (Overload count) id doc (id_loc id))
    | DEF_val (VS_aux (VS_val_spec (_, id, _), annot) as vs) ->
        valspecs := Bindings.add id id !valspecs;
        if !opt_simple_val then Some (latex_command Val id (doc_spec_simple vs) (fst annot))
        else Some (latex_command Val id (Pretty_print_sail.doc_spec vs) (fst annot))
    | DEF_fundef (FD_aux (FD_function (_, _, [FCL_aux (FCL_funcl (id, _), _)]), annot)) ->
        fundefs := Bindings.add id id !fundefs;
        Some (latex_command Function id (Pretty_print_sail.doc_def def) (fst annot))
    | DEF_let (LB_aux (LB_val (pat, _), annot)) ->
        let ids = pat_ids pat in
        begin
          match IdSet.min_elt_opt ids with
          | None -> None
          | Some base_id ->
              letdefs := IdSet.fold (fun id -> Bindings.add id base_id) ids !letdefs;
              Some (latex_command Let base_id (Pretty_print_sail.doc_def def) (fst annot))
        end
    | DEF_type (TD_aux (tdef, annot)) ->
        let id = tdef_id tdef in
        typedefs := Bindings.add id id !typedefs;
        Some (latex_command Type id (Pretty_print_sail.doc_def def) (fst annot))
    | DEF_fundef (FD_aux (FD_function (_, _, funcls), annot)) as def -> Some (latex_funcls def funcls)
    | DEF_pragma ("latex", command, l) -> process_pragma l command
    | DEF_register (DEC_aux (_, annot) as dec) ->
        let id = id_of_dec_spec dec in
        regdefs := Bindings.add id id !regdefs;
        Some (latex_command Register id (Pretty_print_sail.doc_def def) (fst annot))
    | DEF_outcome (OV_aux (OV_outcome (id, _, _), l), _) ->
        outcomedefs := Bindings.add id id !outcomedefs;
        Some (latex_command Outcome id (Pretty_print_sail.doc_def def) l)
    | _ -> None
  in

  let rec process_defs = function
    | [] -> empty
    | def :: defs ->
        let tex = match latex_def def with Some tex -> tex ^^ twice hardline | None -> empty in
        tex ^^ process_defs defs
  in

  let tex = process_defs defs in

  (* Rather than having latex functions that use mangled names, like
     \sailfnmyFunction for a function my_function, we can write
     \sailfn{my_function} by generating a latex macro that compares
     identifiers then outputs the correct mangled command. *)

  (* Accept both the plain identifier and an escaped one that can be used in
     macros that might also typeset the argument. *)
  let add_encoded_ids ids =
    List.concat
      (List.map
         (fun (id, base) ->
           let s = Str.global_replace (Str.regexp_string "#") "\\#" (string_of_id id) in
           let s' = text_code s in
           if String.compare s s' == 0 then [(s, base)] else [(s, base); (s', base)]
         )
         ids
      )
  in

  let id_command cat ids =
    sprintf "\\newcommand{\\%s%s}[1]{\n  " !opt_prefix (category_name cat)
    ^ Util.string_of_list "%\n  "
        (fun (s, id) -> sprintf "\\ifstrequal{#1}{%s}{\\%s}{}" s (latex_cat_id cat id))
        (add_encoded_ids (Bindings.bindings ids))
    ^ "}"
    |> string
  in
  let ref_command cat ids =
    sprintf "\\newcommand{\\%sref%s}[2]{\n  " !opt_prefix (category_name cat)
    ^ Util.string_of_list "%\n  "
        (fun (s, id) -> sprintf "\\ifstrequal{#1}{%s}{\\hyperref[%s]{#2}}{}" s (refcode_cat_id cat id))
        (add_encoded_ids (Bindings.bindings ids))
    ^ "}"
    |> string
  in

  preamble ^^ tex
  ^^ separate (twice hardline)
       [
         id_command Val !valspecs;
         ref_command Val !valspecs;
         id_command Function !fundefs;
         ref_command Function !fundefs;
         id_command Type !typedefs;
         ref_command Type !typedefs;
         id_command Let !letdefs;
         ref_command Let !letdefs;
         id_command Register !regdefs;
         ref_command Register !regdefs;
         id_command Outcome !outcomedefs;
         ref_command Outcome !outcomedefs;
       ]
  ^^ hardline
