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

module type CONVERTER = sig
  type config

  val default_config : loc:Parse_ast.l -> config

  val convert : config -> string -> string
end

module IdentityConverter : CONVERTER = struct
  type config = unit

  let default_config ~loc:_ = ()

  let convert _ comment = comment
end

module AsciidocConverter : CONVERTER = struct
  open Printf
  open Cmarkit

  type config = { this : Ast.id option; loc : Parse_ast.l; list_depth : int }

  let default_config ~loc = { this = None; loc; list_depth = 1 }

  let comment_loc l offset =
    let open Lexing in
    match Reporting.simp_loc l with
    | Some (s, _) ->
        let s = Reporting.Position.advance_position ~trim:false "/*!" s in
        let start_line, start_bol = Textloc.first_line offset in
        let start_cnum = Textloc.first_byte offset in
        let start_bol_offset = if start_line <> 1 then s.pos_cnum - s.pos_bol else 0 in
        let end_line, end_bol = Textloc.last_line offset in
        let end_cnum = Textloc.last_byte offset in
        let end_bol_offset = if end_line <> 1 then s.pos_cnum - s.pos_bol else 0 in
        print_endline (Printf.sprintf "%d %d %d" start_line start_bol start_cnum);
        let sc =
          {
            s with
            pos_lnum = s.pos_lnum + start_line - 1;
            pos_bol = s.pos_bol + start_bol + start_bol_offset;
            pos_cnum = s.pos_cnum + start_cnum;
          }
        in
        let ec =
          {
            s with
            pos_lnum = s.pos_lnum + end_line - 1;
            pos_bol = s.pos_bol + end_bol + end_bol_offset;
            pos_cnum = s.pos_cnum + end_cnum + 1;
          }
        in
        Parse_ast.Range (sc, ec)
    | None -> Parse_ast.Unknown

  let rec format_block buf conf = function
    | Block.Blocks (blocks, _) -> List.iter (format_block buf conf) blocks
    | Block.Paragraph (para, _) ->
        format_inline buf conf (Block.Paragraph.inline para);
        Buffer.add_string buf "\n"
    | Block.Blank_line _ -> Buffer.add_string buf "\n"
    | Block.Code_block (cb, _) -> (
        let code = Block.Code_block.code cb |> List.map Block_line.to_string |> String.concat "\n" in
        match Block.Code_block.info_string cb with
        | None -> ksprintf (Buffer.add_string buf) "----\n%s\n----\n" code
        | Some (lang, _) -> ksprintf (Buffer.add_string buf) "[source,%s]\n----\n%s\n----\n" lang code
      )
    | Block.Heading (h, _) ->
        let equals = String.make (Block.Heading.level h) '=' in
        Buffer.add_string buf equals;
        Buffer.add_char buf ' ';
        format_inline buf conf (Block.Heading.inline h);
        Buffer.add_char buf '\n'
    | Block.Block_quote (bq, _) ->
        Buffer.add_string buf "[quote]\n----\n";
        format_block buf conf (Block.Block_quote.block bq);
        Buffer.add_string buf "\n----\n"
    | b ->
        let offset = Block.meta b |> Meta.textloc in
        let l = comment_loc conf.loc offset in
        raise (Reporting.err_general l "Cannot convert markdown block to Asciidoc")

  and format_inline buf conf = function
    | Inline.Text (str, _) -> Buffer.add_string buf str
    | Inline.Break _ -> Buffer.add_char buf '\n'
    | Inline.Code_span (c, _) -> ksprintf (Buffer.add_string buf) "`%s`" (Inline.Code_span.code c)
    | Inline.Emphasis (emph, _) ->
        Buffer.add_char buf '_';
        format_inline buf conf (Inline.Emphasis.inline emph);
        Buffer.add_char buf '_'
    | Inline.Strong_emphasis (emph, _) ->
        Buffer.add_char buf '*';
        format_inline buf conf (Inline.Emphasis.inline emph);
        Buffer.add_char buf '*'
    | Inline.Inlines (inlines, _) -> List.iter (format_inline buf conf) inlines
    | i ->
        let offset = Inline.meta i |> Meta.textloc in
        let l = comment_loc conf.loc offset in
        raise (Reporting.err_general l "Cannot convert inline markdown element to Asciidoc")

  and format conf doc =
    let buf = Buffer.create 1024 in
    format_block buf conf (Doc.block doc);
    Buffer.contents buf

  let convert conf comment = format conf (Doc.of_string ~strict:true ~locs:true comment)
end
