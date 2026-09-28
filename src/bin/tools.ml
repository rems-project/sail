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
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(****************************************************************************)

open Libsail

module type TOOL = sig
  val options : (Arg.key * Arg.spec * Arg.doc) list

  val run : Yojson.Safe.t option -> string list -> string list -> int
end

let load t fix_options opts =
  let module T = (val t : TOOL) in
  opts := fix_options T.options;
  T.run

module Strip_json_comments : TOOL = struct
  let opt_output : string option ref = ref None
  let opt_compact : bool ref = ref false

  let options =
    [
      ("-o", Arg.String (fun filename -> opt_output := Some filename), "<file> output file (stdout if not provided)");
      ("-compact", Arg.Set opt_compact, " use compact JSON output");
    ]

  let run _ _ = function
    | [file] ->
        let json =
          try Yojson.Safe.from_file ~fname:file ~lnum:0 file
          with Yojson.Json_error message ->
            raise (Reporting.err_general Parse_ast.Unknown (Printf.sprintf "Failed to parse JSON:\n%s" message))
        in
        let close, chan =
          match !opt_output with None -> (false, stdout) | Some out_file -> (true, open_out out_file)
        in
        if !opt_compact then Yojson.Safe.to_channel ~std:true chan json
        else Yojson.Safe.pretty_to_channel ~std:true chan json;
        if close then close_out chan;
        0
    | files ->
        raise
          (Reporting.err_general Parse_ast.Unknown
             (Printf.sprintf "Expected a single input file, got %d" (List.length files))
          )
end

module Format : TOOL = struct
  let opt_format_backup : string option ref = ref None
  let opt_format_only : string list ref = ref []
  let opt_format_emit : string ref = ref "file"
  let opt_format_skip : string list ref = ref []
  let opt_format_debug : bool ref = ref false

  let options =
    [
      ( "-fmt_backup",
        Arg.String (fun suffix -> opt_format_backup := Some suffix),
        "<suffix> create backups of formatted files as 'file.suffix'"
      );
      ("-fmt_only", Arg.String (fun file -> opt_format_only := file :: !opt_format_only), "<file> format only this file");
      ( "-fmt_emit",
        Arg.String (fun output -> opt_format_emit := output),
        "[file(default)|stdout] update target file or just output to stdout"
      );
      ( "-fmt_skip",
        Arg.String (fun file -> opt_format_skip := file :: !opt_format_skip),
        "<file> skip formatting this file"
      );
      ("-fmt_debug", Arg.Bool (fun debug -> opt_format_debug := debug), "<bool> debug mode");
    ]

  let run config variable_assignments frees =
    let is_format_file f =
      match !opt_format_only with [] -> true | files -> List.exists (fun f' -> Sail_file.Path.to_string f = f') files
    in
    let is_skipped_file f =
      match !opt_format_skip with [] -> false | files -> List.exists (fun f' -> Sail_file.Path.to_string f = f') files
    in
    let module Config = struct
      let config =
        match config with
        | Some (`Assoc keys) ->
            List.assoc_opt "fmt" keys |> Option.map Format_sail.config_from_json
            |> Option.value ~default:Format_sail.default_config
        | Some _ -> raise (Reporting.err_general Parse_ast.Unknown "Invalid configuration file (must be a json object)")
        | None -> Format_sail.default_config
    end in
    let module Formatter = Format_sail.Make (Config) in
    let project_files, files = List.partition (fun free -> Filename.check_suffix free ".sail_project") frees in

    (* Get all the files references by project files *)
    let referenced_files =
      List.map
        (fun project_file ->
          let root_directory = Filename.dirname project_file in
          let defs =
            Project.mk_root root_directory :: Initial_check.parse_project (Sail_file.Path.actual project_file)
          in

          let variables = ref Util.StringMap.empty in
          List.iter
            (fun assignment ->
              if not (Project.parse_assignment ~variables assignment) then
                raise (Reporting.err_general Parse_ast.Unknown ("Could not parse assignment " ^ assignment))
            )
            variable_assignments;
          let proj = Project.initialize_project_structure ~variables defs in
          Project.all_files proj
        )
        project_files
      |> List.concat |> List.map fst
    in

    let parsed_files =
      List.map (fun f -> (f, Initial_check.parse_file f)) (List.map Sail_file.Path.actual files @ referenced_files)
    in
    List.iter
      (fun (f, (comments, parse_ast)) ->
        let source = Sail_file.contents (Sail_file.open_file f) in
        if is_format_file f && not (is_skipped_file f) then (
          let formatted =
            Formatter.format_defs ~debug:!opt_format_debug (Sail_file.Path.to_string f) source comments parse_ast
          in
          ( match !opt_format_backup with
          | Some suffix ->
              let out_chan = open_out (Sail_file.Path.to_string f ^ "." ^ suffix) in
              output_string out_chan source;
              close_out out_chan
          | None -> ()
          );
          match !opt_format_emit with
          | "file" ->
              let file_info = Util.open_output_with_check (Sail_file.Path.to_string f) in
              output_string file_info.channel formatted;
              Util.close_output_with_check file_info
          | "stdout" ->
              output_string stdout formatted;
              flush stdout
          | _ -> raise (Failure "unknown format_emit option")
        )
      )
      parsed_files;
    0
end

module Extern_json : TOOL = struct
  open Parse_ast

  let opt_output : string option ref = ref None
  let opt_compact : bool ref = ref false
  let opt_exclude : string list ref = ref []

  let options =
    [
      ("-o", Arg.String (fun filename -> opt_output := Some filename), "<file> output file (stdout if not provided)");
      ("-compact", Arg.Set opt_compact, " use compact JSON output");
      ( "-exclude",
        Arg.String (fun path -> opt_exclude := path :: !opt_exclude),
        "<file> exclude this file from the output"
      );
    ]

  (* A conditional compilation directive that encloses a definition,
     along with which branch of the directive the definition occurs
     in. For $iftarget we record the targets it applies to, with any
     target sets expanded. *)
  type test = Ifdef of string | Ifndef of string | Iftarget of string list

  type condition = { test : test; in_else : bool }

  let json_of_condition c =
    let test =
      match c.test with
      | Ifdef symbol -> [("directive", `String "ifdef"); ("argument", `String symbol)]
      | Ifndef symbol -> [("directive", `String "ifndef"); ("argument", `String symbol)]
      | Iftarget targets ->
          [("directive", `String "iftarget"); ("targets", `List (List.map (fun t -> `String t) targets))]
    in
    `Assoc (test @ [("branch", `String (if c.in_else then "else" else "then"))])

  (* Target sets defined by $target_set directives in all the input
     files, mapping each set name to the targets it contains. *)
  let target_sets : (string, string list) Hashtbl.t = Hashtbl.create 16

  let words s = String.split_on_char ' ' s |> List.filter (fun w -> not (String.equal w ""))

  (* Expand any target set names in a space-separated list of targets. *)
  let expand_targets s =
    words s
    |> List.concat_map (fun t -> Option.value ~default:[t] (Hashtbl.find_opt target_sets t))
    |> List.fold_left (fun acc t -> if List.exists (String.equal t) acc then acc else t :: acc) []
    |> List.rev

  (* Expand extern bindings for target sets into a binding for each
     target in the set. A binding for a specific target takes
     precedence over one from a target set, and otherwise the first
     binding for a target wins. *)
  let expand_bindings bindings =
    let explicit = List.filter (fun (target, _) -> not (Hashtbl.mem target_sets target)) bindings in
    List.fold_left
      (fun acc (target, binding) ->
        let bound t = List.exists (fun (t', _) -> String.equal t t') acc in
        match Hashtbl.find_opt target_sets target with
        | Some targets ->
            let targets =
              List.filter (fun t -> not (List.exists (fun (t', _) -> String.equal t t') explicit || bound t)) targets
            in
            List.rev_map (fun t -> (t, binding)) targets @ acc
        | None -> if bound target then acc else (target, binding) :: acc
      )
      [] bindings
    |> List.rev

  (* Translation of Sail types into the OCaml types used by the OCaml
     backend and Sail_lib. This follows Rewrites.simple_typ and
     Ocaml_backend.ocaml_typ, but works over un-typechecked parse
     ASTs. *)

  exception Unsupported_type

  let string_of_kid (Kid_aux (Var v, _)) = v

  let string_of_id (Id_aux ((Id x | Operator x), _)) = x

  (* Type synonyms collected from all the input files, mapping each
     synonym to its parameters and definition. *)
  let synonyms : (string, kid list * atyp) Hashtbl.t = Hashtbl.create 64

  let rec collect_definitions (DEF_aux (aux, l)) =
    match aux with
    | DEF_pragma ("target_set", Pragma_line (arg, _)) ->
        let set, targets = Initial_check.parse_target_set l arg in
        Hashtbl.replace target_sets set targets
    | DEF_type (TD_aux (TD_abbrev (id, TypQ_aux (typq, _), _, atyp), _)) ->
        let params =
          match typq with
          | TypQ_no_forall -> []
          | TypQ_tq qis ->
              List.concat_map
                (function QI_aux (QI_id (KOpt_aux (KOpt_kind (_, kids, _, _), _)), _) -> kids | _ -> [])
                qis
        in
        Hashtbl.replace synonyms (string_of_id id) (params, atyp)
    | DEF_private def | DEF_attribute (_, def) | DEF_doc (_, def) -> collect_definitions def
    | _ -> ()

  let parens_if b s = if b then "(" ^ s ^ ")" else s

  (* When nested is true the type appears as a tuple component,
     function argument, or type constructor argument, so tuples and
     functions must be parenthesized.

     The substitution maps the parameters of any type synonyms being
     expanded to their translated arguments. These are lazy, as
     numeric arguments cannot be translated, but will also never be
     used in a type position. *)
  let rec ocaml_type ?(nested = false) subst (ATyp_aux (aux, l)) =
    match aux with
    | ATyp_parens atyp | ATyp_infix [(IT_primary atyp, _, _)] | ATyp_exist (_, _, atyp) -> ocaml_type ~nested subst atyp
    | ATyp_var kid -> (
        match List.assoc_opt (string_of_kid kid) subst with Some typ -> Lazy.force typ | None -> string_of_kid kid
      )
    | ATyp_nset _ -> "Z.t"
    | ATyp_id id -> ocaml_type_app subst l id []
    | ATyp_app (id, args) -> ocaml_type_app subst l id args
    | ATyp_tuple atyps -> parens_if nested (String.concat " * " (List.map (ocaml_type ~nested:true subst) atyps))
    | ATyp_fn (arg, ret, _) ->
        let args = match arg with ATyp_aux (ATyp_tuple args, _) -> args | arg -> [arg] in
        parens_if nested (String.concat " -> " (List.map (ocaml_type ~nested:true subst) args @ [ocaml_type subst ret]))
    | _ -> raise Unsupported_type

  and ocaml_type_app subst l id args =
    let elem atyp = ocaml_type ~nested:true subst atyp in
    match (string_of_id id, args) with
    | ("int" | "nat" | "atom" | "range" | "implicit"), _ -> "Z.t"
    | ("bool" | "atom_bool"), _ -> "bool"
    | "bitvector", _ -> "bits"
    | ("string" | "string_literal"), [] -> "string"
    | "unit", [] -> "unit"
    | "real", [] -> "Q.t"
    | "list", [atyp] -> elem atyp ^ " list"
    (* The element type is the last argument, with the optional order argument before it *)
    | "vector", [_; atyp] | "vector", [_; _; atyp] -> elem atyp ^ " list"
    | "register", [atyp] -> elem atyp ^ " ref"
    | name, _ -> (
        match Hashtbl.find_opt synonyms name with
        | Some (params, body) when Int.equal (List.compare_lengths params args) 0 ->
            let subst' = List.map2 (fun param arg -> (string_of_kid param, lazy (elem arg))) params args in
            ocaml_type subst' body
        | _ -> raise Unsupported_type
      )

  let ocaml_type_of_typschm (TypSchm_aux (TypSchm_ts (_, atyp), _)) =
    try `String (ocaml_type [] atyp) with Unsupported_type -> `Null

  let collapse_whitespace s =
    String.split_on_char '\n' s
    |> List.concat_map (String.split_on_char ' ')
    |> List.concat_map (String.split_on_char '\t')
    |> List.filter (fun w -> not (String.equal w ""))
    |> String.concat " "

  let source_text l =
    match Reporting.simp_loc l with
    | Some (p1, p2) -> Some (collapse_whitespace (Reporting.loc_range_to_src p1 p2))
    | None -> None

  let json_of_extern ~file ~conditions typschm id (ext : extern) =
    let name, is_operator = match id with Id_aux (Id x, _) -> (x, false) | Id_aux (Operator x, _) -> (x, true) in
    let (TypSchm_aux (_, typ_l)) = typschm in
    `Assoc
      [
        ("name", `String name);
        ("operator", `Bool is_operator);
        ("pure", `Bool ext.pure);
        ( "bindings",
          `Assoc (List.map (fun (target, binding) -> (target, `String binding)) (expand_bindings ext.bindings))
        );
        ("type", match source_text typ_l with Some txt -> `String txt | None -> `Null);
        ("ocaml_type", ocaml_type_of_typschm typschm);
        ("file", `String file);
        ("conditions", `List (List.rev_map json_of_condition conditions));
      ]

  (* Walk the un-preprocessed definitions of a file, keeping track of
     the stack of enclosing conditional directives (innermost first). *)
  let externs_in_file file defs =
    let externs = ref [] in
    let conditions = ref [] in
    let rec go (DEF_aux (aux, l)) =
      match aux with
      | DEF_val (VS_aux (VS_val_spec (typschm, id, Some ext), _)) ->
          externs := json_of_extern ~file ~conditions:!conditions typschm id ext :: !externs
      | DEF_pragma ("ifdef", Pragma_line (symbol, _)) ->
          conditions := { test = Ifdef (String.trim symbol); in_else = false } :: !conditions
      | DEF_pragma ("ifndef", Pragma_line (symbol, _)) ->
          conditions := { test = Ifndef (String.trim symbol); in_else = false } :: !conditions
      | DEF_pragma ("iftarget", Pragma_line (targets, _)) ->
          conditions := { test = Iftarget (expand_targets targets); in_else = false } :: !conditions
      | DEF_pragma ("else", _) -> (
          match !conditions with
          | c :: cs -> conditions := { c with in_else = true } :: cs
          | [] -> raise (Reporting.err_general l "$else without matching $ifdef, $ifndef, or $iftarget")
        )
      | DEF_pragma ("endif", _) -> (
          match !conditions with
          | _ :: cs -> conditions := cs
          | [] -> raise (Reporting.err_general l "$endif without matching $ifdef, $ifndef, or $iftarget")
        )
      | DEF_outcome (_, defs) -> List.iter go defs
      | DEF_private def | DEF_attribute (_, def) | DEF_doc (_, def) -> go def
      | _ -> ()
    in
    List.iter go defs;
    List.rev !externs

  (* Expand any directories given on the command line into the Sail
     files they (recursively) contain. *)
  let rec expand_path path =
    if Sys.file_exists path && Sys.is_directory path then
      Sys.readdir path |> Array.to_list |> List.sort String.compare
      |> List.concat_map (fun entry ->
          let entry = Filename.concat path entry in
          if Sys.is_directory entry || Filename.check_suffix entry ".sail" then expand_path entry else []
      )
    else [path]

  let run _ _ frees =
    (* Sail_file.open_file canonicalizes paths, so comparing handles
       lets us exclude files regardless of how their paths are written. *)
    let excluded =
      List.map
        (fun file ->
          if not (Sys.file_exists file) then
            raise (Reporting.err_general Parse_ast.Unknown ("Excluded file " ^ file ^ " does not exist"));
          Sail_file.open_file (Sail_file.Path.actual file)
        )
        !opt_exclude
    in
    let files =
      List.concat_map expand_path frees
      |> List.filter (fun file ->
          let handle = Sail_file.open_file (Sail_file.Path.actual file) in
          not (List.exists (Sail_file.handle_equal handle) excluded)
      )
    in
    let parsed = List.map (fun file -> (file, snd (Initial_check.parse_file (Sail_file.Path.actual file)))) files in
    (* Collect type synonyms and target sets from every file first, as they may be used before (or in a different file
       to) where they are defined *)
    List.iter (fun (_, defs) -> List.iter collect_definitions defs) parsed;
    let externs = List.concat_map (fun (file, defs) -> externs_in_file file defs) parsed in
    let json = `Assoc [("externs", `List externs)] in
    let close, chan = match !opt_output with None -> (false, stdout) | Some out_file -> (true, open_out out_file) in
    if !opt_compact then Yojson.Safe.to_channel ~std:true chan json
    else Yojson.Safe.pretty_to_channel ~std:true chan json;
    output_char chan '\n';
    if close then close_out chan;
    0
end
