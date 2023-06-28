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

let opt_doc_format = ref "asciidoc"
let opt_doc_files = ref []
let opt_doc_embed = ref None
let opt_doc_compact = ref false
let opt_doc_bundle = ref "doc.json"

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
    ("-doc_compact", Arg.Unit (fun _ -> opt_doc_compact := true), " Use compact documentation format");
    ("-doc_bundle", Arg.String (fun file -> opt_doc_bundle := file), "<file> Name for documentation bundle file");
  ]

let output_docinfo doc_dir docinfo =
  let chan = open_out (Filename.concat doc_dir !opt_doc_bundle) in
  let json = Docinfo.docinfo_to_json docinfo in
  if !opt_doc_compact then Yojson.to_channel ~std:true chan json else Yojson.pretty_to_channel ~std:true chan json;
  output_char chan '\n';
  close_out chan

let doc_target _ _ out_file ast _ _ =
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
    end in
    let module Gen = Docinfo.Generator (Markdown.AsciidocConverter) (Config) in
    let docinfo = Gen.docinfo_for_ast ~files:!opt_doc_files ~hyperlinks:Docinfo.hyperlinks_from_def ast in
    output_docinfo doc_dir docinfo
  else if !opt_doc_format = "identity" then
    let module Config = struct
      let embedding_mode = embedding_option ()
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
