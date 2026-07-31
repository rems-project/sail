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

let load t fix_options opts =
  let module T = (val t : TOOL) in
  opts := fix_options T.options;
  T.run
