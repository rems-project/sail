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

open Interactive.State

let opt_doc_format = ref "asciidoc"
let opt_doc_files = ref []
let opt_doc_embed = ref None
let opt_doc_embed_with_location = ref false
let opt_doc_compact = ref false
let opt_doc_bundle = ref "doc.json"

let opt_html_css = ref None
let opt_html_link_prefix = ref "../"

let embedding_option () =
  match !opt_doc_embed with
  | None -> None
  | Some "plain" -> Some Docinfo.Plain
  | Some "base64" -> Some Docinfo.Base64
  | Some embedding ->
      Printf.eprintf "Unknown embedding type %s for -doc_embed, allowed values are 'plain' or 'base64'\n" embedding;
      exit 1

let doc_options =
  [
    ( "-doc_format",
      Arg.String (fun format -> opt_doc_format := format),
      "<format> Output documentation in the chosen format, either latex or asciidoc (default asciidoc)"
    );
    ( "-doc_file",
      Arg.String (fun file -> opt_doc_files := file :: !opt_doc_files),
      "<file> Document only the provided files"
    );
    ( "-doc_embed",
      Arg.String (fun format -> opt_doc_embed := Some format),
      "<plain|base64> Embed all documentation contents into the documentation bundle rather than referencing it"
    );
    ( "-doc_embed_with_location",
      Arg.Set opt_doc_embed_with_location,
      " When used with --doc-embed, include both the contents and locations"
    );
    ("-doc_compact", Arg.Unit (fun _ -> opt_doc_compact := true), " Use compact documentation format");
    ("-doc_bundle", Arg.String (fun file -> opt_doc_bundle := file), "<file> Name for documentation bundle file");
  ]

let output_docinfo doc_dir docinfo =
  let chan = open_out (Filename.concat doc_dir !opt_doc_bundle) in
  let json = Docinfo.json_of_docinfo docinfo in
  if !opt_doc_compact then Yojson.Basic.to_channel ~std:true chan json
  else Yojson.Basic.pretty_to_channel ~std:true chan json;
  output_char chan '\n';
  close_out chan

let doc_target out_file { ast; _ } =
  Reporting.opt_warnings := true;
  let doc_dir = match out_file with None -> "sail_doc" | Some s -> s in
  begin
    try
      if not (Sys.is_directory doc_dir) then (
        prerr_endline ("Failure: documentation output location exists and is not a directory: " ^ doc_dir);
        exit 1
      )
    with Sys_error _ -> Unix.mkdir doc_dir 0o755
  end;
  if !opt_doc_format = "asciidoc" || !opt_doc_format = "adoc" then
    let module Config = struct
      let embedding_mode = embedding_option ()
      let embed_with_location = !opt_doc_embed_with_location
    end in
    let module Gen = Docinfo.Generator (Markdown.AsciidocConverter) (Config) in
    let docinfo = Gen.docinfo_for_ast ~files:!opt_doc_files ~hyperlinks:Docinfo.hyperlinks_from_def ast in
    output_docinfo doc_dir docinfo
  else if !opt_doc_format = "identity" then
    let module Config = struct
      let embedding_mode = embedding_option ()
      let embed_with_location = !opt_doc_embed_with_location
    end in
    let module Gen = Docinfo.Generator (Markdown.IdentityConverter) (Config) in
    let docinfo = Gen.docinfo_for_ast ~files:!opt_doc_files ~hyperlinks:Docinfo.hyperlinks_from_def ast in
    output_docinfo doc_dir docinfo
  else Printf.eprintf "Unknown documentation format: %s\n" !opt_doc_format

let _ =
  Target.register ~name:"doc" ~options:doc_options
    ~pre_parse_hook:(fun () ->
      Type_check.opt_expand_valspec := false;
      Type_check.opt_no_bitfield_expansion := true
    )
    doc_target

let html_options =
  [
    ("-html_css", Arg.String (fun file -> opt_html_css := Some file), "<file> CSS file for html output");
    ( "-html_link_prefix",
      Arg.String (fun prefix -> opt_html_link_prefix := prefix),
      "<string> Prefix links in HTML output with string"
    );
  ]

let rec create_directories path =
  match Sys.is_directory path with
  | true -> ()
  | false -> raise (Reporting.err_general Parse_ast.Unknown ("Failure: Path " ^ path ^ " exists and is not a directory"))
  | exception Sys_error _ ->
      let parent = Filename.dirname path in
      create_directories parent;
      Unix.mkdir path 0o755

let html_target files out_dir_opt { ast; _ } =
  let open Html_source in
  Reporting.opt_warnings := true;
  let out_dir = match out_dir_opt with None -> "sail_doc" | Some s -> s in
  let link_targets = hyperlink_targets ast in
  List.iter
    (fun file_info ->
      let output_file = Filename.concat out_dir (file_info.prefix ^ ".html") in
      create_directories (Filename.dirname output_file);
      let ((out_chan, _, _, _) as handle) = Util.open_output_with_check_unformatted None output_file in
      let file_links = Html_source.hyperlinks_for_file ~filename:file_info.filename ast in
      let file_links =
        Array.map
          (fun (node, s, e) ->
            match Callgraph.NodeMap.find_opt node link_targets with
            | Some p ->
                let filename = p.Lexing.pos_fname in
                begin
                  match List.find_opt (fun info -> info.filename = filename) !files with
                  | Some info ->
                      Some (Printf.sprintf "%s%s.html#L%d" !opt_html_link_prefix info.prefix p.Lexing.pos_lnum, s, e)
                  | None -> None
                end
            | None -> None
          )
          file_links
      in
      let file_links = file_links |> Array.to_seq |> Seq.filter_map (fun x -> x) |> Array.of_seq in
      let css =
        try Option.map Util.read_whole_file !opt_html_css
        with Sys_error msg -> raise (Reporting.err_general Parse_ast.Unknown msg)
      in
      output_html ?css ~file_info ~hyperlinks:file_links out_chan;
      Util.close_output_with_check handle
    )
    !files

let _ =
  let files : Html_source.file_info list ref = ref [] in
  Target.register ~name:"html" ~options:html_options
    ~pre_initial_check_hook:(fun filenames ->
      List.iter
        (fun filename ->
          match Filename.chop_suffix_opt ~suffix:".sail" filename with
          | Some prefix when Filename.is_relative filename ->
              let contents = Util.read_whole_file filename in
              let highlights = Html_source.highlights ~filename ~contents in
              files := { filename; prefix; contents; highlights } :: !files
          | _ -> ()
        )
        filenames
    )
    (html_target files)
