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

(** Automatic formatting for the LSP (the [textDocument/formatting] and [textDocument/rangeFormatting] requests). *)

(** Format an entire document using the same formatter as [sail -fmt], returning the edits that turn the buffer into its
    formatted form: a single whole-document replacement, or no edits at all when the buffer is already formatted.
    Formatting requires the buffer to parse, so a document with a syntax error - or one the formatter rejects - returns
    the error explaining why it could not be formatted. *)
val compute : config:Format_sail.config -> Sail_file.handle -> (Lsp.Types.TextEdit.t list, Reporting.error) Result.t

(** Format the definitions a range touches, one edit per definition, leaving the rest of the document alone. A range
    that selects no definition - a cursor in a comment sitting between two of them, say - yields no edits. The whole
    buffer still has to parse, as it does for [compute], because a definition is formatted by formatting the document it
    belongs to and keeping the part of the result that corresponds to it. *)
val compute_range :
  config:Format_sail.config ->
  range:Lsp.Types.Range.t ->
  Sail_file.handle ->
  (Lsp.Types.TextEdit.t list, Reporting.error) Result.t
