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
open Log

(* Parse and format the buffer. Raises [Reporting.Fatal_error] if the buffer does
   not parse, or if the formatter rejects its own output. *)
let format_buffer ~config handle =
  let module Formatter = Format_sail.Make (struct
    let config = config
  end) in
  let filename = Sail_file.Path.to_string (Sail_file.to_path handle) in
  let source = Sail_file.contents handle in
  let comments, defs = Initial_check.parse_file_from_string source in
  (source, defs, Formatter.format_defs filename source comments defs)

(* An LSP position for a position within [source]. The parse that produced it is
   of a string rather than of a file in the editor's view of the world, so the
   conversion to editor coordinates - a line plus an offset in UTF-16 code units
   - is done here against the same string, rather than by [Sail_file]. *)
let editor_position source (p : Sail_file.position) =
  let open Sail_file.Position in
  let bol = min p.pos_bol (String.length source) in
  let cnum = min (max p.pos_cnum bol) (String.length source) in
  Lsp.Types.Position.create ~line:(p.pos_lnum - 1)
    ~character:(Sail_file.utf16_length (String.sub source bol (cnum - bol)))

(* The end of the buffer as an LSP position. [Sail_file.contents] joins the lines
   with '\n', so the last element of the split is the final line. *)
let end_position source =
  let rec last = function [] -> "" | [line] -> line | _ :: lines -> last lines in
  let lines = String.split_on_char '\n' source in
  Lsp.Types.Position.create ~line:(List.length lines - 1) ~character:(Sail_file.utf16_length (last lines))

let whole_document source =
  Lsp.Types.Range.create ~start:(Lsp.Types.Position.create ~line:0 ~character:0) ~end_:(end_position source)

let compute ~config handle =
  match format_buffer ~config handle with
  | exception Reporting.Fatal_error err -> Error err
  (* An unchanged buffer means no edits, rather than an edit that rewrites the
     whole document with what it already contains. *)
  | source, _, formatted when String.equal formatted source -> Ok []
  | source, _, formatted -> Ok [Lsp.Types.TextEdit.create ~newText:formatted ~range:(whole_document source)]

let def_loc (Parse_ast.DEF_aux (_, l)) = l

(* The extent of a definition in the source it was parsed from. A definition with
   attributes, a doc comment or a [private] marker attached to it is a definition
   wrapped in another one, and the wrapper's location spans only the wrapper
   itself - the [$[attr]] and not what it is attached to - so the extent has to
   be stitched together from the wrapper and the definition inside it. *)
let rec def_extent (Parse_ast.DEF_aux (aux, l)) =
  let wrapper = Reporting.simp_loc l in
  match aux with
  | Parse_ast.DEF_private def | Parse_ast.DEF_attribute (_, def) | Parse_ast.DEF_doc (_, def) -> (
      match (wrapper, def_extent def) with
      | Some (p1, _), Some (_, p2) -> Some (p1, p2)
      | Some _, None -> wrapper
      | None, extent -> extent
    )
  | _ -> wrapper

(* Whether a definition is one the request selected. Definitions start on a line
   of their own, so whole lines are the right granularity: a request touching any
   part of a line selects the definition that line belongs to, which makes an
   empty range - a bare cursor - select the definition it sits in. *)
let selected (range : Lsp.Types.Range.t) (p1 : Sail_file.position) (p2 : Sail_file.position) =
  let open Sail_file.Position in
  (* Lexing lines are 1-based, editor lines are 0-based. *)
  p1.pos_lnum - 1 <= range.end_.line && range.start.line <= p2.pos_lnum - 1

(* The text of a definition, cut out of the string it was parsed from. *)
let def_text source p1 p2 =
  let open Sail_file.Position in
  String.sub source p1.pos_cnum (p2.pos_cnum - p1.pos_cnum)

(* Replace each selected definition with its formatted counterpart. The edits do
   not overlap - definitions do not - and are all relative to the buffer as it
   stands, as LSP requires. *)
let def_edits ~range source formatted defs formatted_defs =
  let edit (def, formatted_def) =
    match (def_extent def, def_extent formatted_def) with
    (* A definition without a usable source range is one we cannot place an edit
       against, e.g. one that came from a $include rather than from the buffer. *)
    | Some (p1, p2), Some (f1, f2) when selected range p1 p2 ->
        (* The formatter promises the syntax tree survives formatting, so the two
           definitions must be the same one. If they ever are not, replacing the
           text of one with the text of the other would silently corrupt the
           buffer, so refuse rather than guess. *)
        if Option.is_some (Parse_ast_diff.diff_def def formatted_def) then
          Error
            (Reporting.Err_general
               (def_loc def, "Formatting changed this definition, so it cannot be formatted on its own")
            )
        else (
          let source_text = def_text source p1 p2 in
          let formatted_text = def_text formatted f1 f2 in
          if String.equal source_text formatted_text then Ok None
          else (
            let range = Lsp.Types.Range.create ~start:(editor_position source p1) ~end_:(editor_position source p2) in
            Ok (Some (Lsp.Types.TextEdit.create ~newText:formatted_text ~range))
          )
        )
    | _ -> Ok None
  in
  let rec collect edits = function
    | [] -> Ok (List.rev edits)
    | pair :: pairs -> (
        match edit pair with
        | Error _ as err -> err
        | Ok None -> collect edits pairs
        | Ok (Some edit) -> collect (edit :: edits) pairs
      )
  in
  collect [] (List.combine defs formatted_defs)

let compute_range ~config ~range handle =
  match
    let source, defs, formatted = format_buffer ~config handle in
    let _, formatted_defs = Initial_check.parse_file_from_string formatted in
    (source, defs, formatted, formatted_defs)
  with
  | exception Reporting.Fatal_error err -> Error err
  | source, defs, formatted, formatted_defs ->
      if List.compare_lengths defs formatted_defs <> 0 then
        Error (Reporting.Err_general (Parse_ast.Unknown, "Formatting changed the number of definitions in the file"))
      else def_edits ~range source formatted defs formatted_defs
