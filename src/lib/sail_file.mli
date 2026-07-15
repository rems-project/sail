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

(** This module contains all the logic for working with source files. *)

(** {1 File paths} *)

(** As per the OCaml stdlib [Filename] module, paths are represented by strings.

    The one difference is we split files between 'actual' file, i.e. those that actually exist on the file system and
    have real paths, from 'virtual' files which do not actually exist.

    Any file that is embedded into the sail binary using the [sail_maker embed] is virtual, as is the ARGV string and
    the REPL contents. There is also a dummy empty file, which is used by the [Initial_check] helper functions that
    parse expressions directly from strings. *)
module Path : sig
  type t

  val actual : string -> t

  val is_virtual : t -> bool

  val map_actual : (string -> string) -> t -> t

  val to_string : t -> string
end

type path = Path.t

(** {1 Handles} *)

(** Handles are references to opened files that we have read. See [open_file]. *)
type handle = private int

val handle_compare : handle -> handle -> int

module HandleSet : sig
  include Set.S with type elt = handle
end

(** Open a file and return a [handle] to it's contents. Note that the file is not actually held open -- we read the
    contents, then close the handle storing the file information and contents in memory. As such there is no close_file.
    Repeatedly calling this file on the same string will return the same handle. *)
val open_file : path -> handle

val add_virtual_file : contents:string -> string -> path * handle

val get_virtual_file : string -> handle option

(** The path that was passed to [open_file], or in the case of [add_virtual_file] was created at the same time as the
    handle. *)
val to_path : handle -> path

(** The contents of a Sail file as a string, without any pending edits (see the LSP section of this file). *)
val contents : handle -> string

(** {2 Special handles} *)

(** This is special handle that resolves to a internal file that is always empty. *)
val dummy : handle

(** This is a special handle that contains inputs to the sail -i REPL. *)
val interactive_repl : handle

val repl_prompt_line : unit -> int

val add_to_repl_contents : command:string -> int * int

(** This is a special handle that treats the Sail argv array as a file for error reporting, with one member of the argv
    array per line. *)
val argv : handle

(** This returns the argv array used by Sail. It combines OCaml's Sys.argv with the value of either SAIL_ENCODED_FLAGS
    (arguments separated by the ASCII unit separator [0x1f]) or SAIL_FLAGS (space separated) using the first only if
    both are present. *)
val sail_argv : unit -> string Array.t

(** {1 File positions}

    This module mirrors the OCaml builtin Lexing position type almost exactly, providing a drop-in replacement. The key
    difference is pos_fname is actually a handle, rather than just a filename.

    Note that then Menhir parsers and OCamllex generated lexers do still use [Lexing.position], they just never use the
    pos_fname field for that type.

    Positions do not necessarily correspond to sensible locations in any file, users should not naively assume that the
    positions are actually in-bounds for the provided handle contents. *)
module Position : sig
  type position = { pos_fname : handle; pos_lnum : int; pos_bol : int; pos_cnum : int }

  (** Convert a OCamllex [Lexing] position to a Sail one, discarding the string pos_fname. *)
  val from_lexing : handle -> Lexing.position -> position

  (** Convert a Sail position back into an OCamllex [Lexing] position. The [pos_fname] field is set to the empty string.
      Used to feed positions back into the lexbuf and Menhir's incremental API, where [from_lexing] will re-attach the
      correct handle. *)
  val to_lexing : position -> Lexing.position

  (** A dummy (invalid) position in the the [dummy] file. *)
  val dummy_pos : position
end

type position = Position.position

(** Returns the byte-offset for a line number. *)
val bol_of_lnum : int -> handle -> int option

(** Replace the contents of a file. Note that this only changes the in-memory contents of the file, and does not flush
    the changes to disk. *)
val write_file : contents:string -> handle -> unit

(** {1 Language-server-protocol (LSP) file lifecycle} *)

(** The LSP takes control of a file by sending us a DidOpenTextDocument message, with the contents of the file as seen
    by the editor. *)
val editor_take_file : contents:string -> string -> handle

(** The LSP can stop editing a file using the DidCloseTextDocument message, in which case we need to manage the file. *)
val editor_drop_file : handle -> unit

(** The LSP protocol uses line + character offsets as positions. Both are zero-based, and [character] is counted in
    UTF-16 code units (as the LSP protocol specifies), not bytes. The conversion to the byte offsets Sail's lexer uses
    happens lazily, when edits are applied and in [editor_position] and [lexing_position]. *)
type editor_position = { line : int; character : int }

type editor_range = editor_position * editor_position

(** Note that the empty string represents a delete operation as per LSP. *)
type text_edit = { range : editor_range; text : string }

type text_edit_size = Single_line of int | Multiple_lines of { pre : int; newlines : int; post : int }

(** Store a pending text edit to a file. This is used by [editor_position] and [lexing_position] to synchonize locations
    between the last type-checked version of the file, and any changes that have subsequently been made in the editor.
    Note that it does not change the actual contents of the file. *)
val edit_file : handle -> text_edit -> unit

(** Take a Sail AST position, and return the where it will visibly appear in the user's editor. Returns None if the
    position no longer exists in the editor buffer, for example, the user may have deleted the position. *)
val editor_position : position -> editor_position option

(** Take a cursor position in the editor, and map it to a position in the Sail AST. Returns None if the cursor position
    is within a pending edit that has not yet been processed by Sail. *)
val lexing_position : handle -> editor_position -> position option

(** Bake the queued edits (see [edit_file]) into the file's contents, bringing them in sync with the editor, and clear
    the queue. This is where the UTF-16 code-unit offsets carried by edits are resolved to byte offsets. *)
val apply_edits : handle -> unit

(** The length of a UTF-8 string in UTF-16 code units. LSP character offsets and lengths are counted in UTF-16 code
    units, so this converts a byte length (or, applied to a substring, a byte offset) into the LSP's units. *)
val utf16_length : string -> int

(** {1 Channel interface} *)

(** This module aims to provide a drop-in replacement for the stdlib in_channel functionality used by Sail, essentially
    providing an iterator style interface to the file contents. *)
module In_channel : sig
  type t

  val from_file : handle -> t

  val input_line_opt : t -> string option

  val input_line : t -> string
end
