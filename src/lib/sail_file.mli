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

type handle = private int

(** This is a special handle that contains inputs to the sail -i REPL *)
val interactive_repl : handle

(** This is a special handle that treats the Sail argv array as a file for error reporting *)
val argv : handle

val repl_prompt_line : unit -> int

val add_to_repl_contents : command:string -> int * int

val bol_of_lnum : int -> handle -> int option

(** For the LSP, we might have Sail and the editor use slightly
    different paths for the same file so we can set this to
    Sys.realpath, and we will then treat files with the same canonical
    name as the same file.

    We can't just use realpath directly because it would mean
    increasing our minimum OCaml version to 4.13. *)
val set_canonicalize_function : (string -> string) -> unit

(** Open a file and return a 'handle' to it's contents. Note that the
    file is not actually held open -- we read the contents, then close
    the handle storing the file information and contents in memory. As
    such there is no close_file. Repeatedly calling this file on the
    same string (as determined by [set_canonicalize_function]) will
    return the same handle. *)
val open_file : string -> handle

(** Replace the contents of a file. Note that this only changes the
    in-memory contents of the file, and does not flush the changes to
    disk. *)
val write_file : contents:string -> handle -> unit

(** The the LSP takes control of a file by sending us a
    DidOpenTextDocument message, with the contents of the file as seen
    by the editor. *)
val editor_take_file : contents:string -> string -> handle

(** The LSP can stop editing a file using the DidCloseTextDocument
    message, in which case we need to manage the file. *)
val editor_drop_file : handle -> unit

(** The LSP protocol uses line + character offsets as positions *)
type editor_position = { line : int; character : int }

type editor_range = editor_position * editor_position

(** Note that the empty string represents a delete operation as per
    LSP. *)
type text_edit = { range : editor_range; text : string }

type text_edit_size = Single_line of int | Multiple_lines of { pre : int; newlines : int; post : int }

(** Store a pending text edit to a file. This is used by
    [editor_position] and [lexing_position] to synchonize locations
    between the last type-checked version of the file, and any changes
    that have subsequently been made in the editor. Note that it does
    not change the actual contents of the file. *)
val edit_file : handle -> text_edit -> unit

(** Take a Sail AST position, and return the where it will visibly
    appear in the user's editor. Returns None if the position no
    longer exists in the editor buffer, for example, the user may have
    deleted the position. *)
val editor_position : Lexing.position -> editor_position option

(** Take a cursor position in the editor, and map it to a position in
    the Sail AST. Returns None if the cursor position is within a
    pending edit that has not yet been processed by Sail. *)
val lexing_position : handle -> editor_position -> Lexing.position option

(** The contents of a Sail file as a string, without any pending
    edits. *)
val contents : handle -> string

(** This module aims to provide a drop-in replacement for the stdlib
    in_channel functionality used by Sail, essentially providing an
    iterator style interface to the file contents. *)
module In_channel : sig
  type t

  val from_file : handle -> t

  val input_line_opt : t -> string option

  val input_line : t -> string
end
