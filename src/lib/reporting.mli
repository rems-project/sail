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

(** Sail error reporting

  [Reporting] contains functions to report errors and warnings.
  It contains functions to print locations ([Parse_ast.l] and [Ast.l]) and lexing positions.

  The main functionality is reporting errors. This is done by raising a
  [Fatal_error] exception. This is caught internally and reported via [report_error].
  There are several predefined types of errors which all cause different error
  messages. If none of these fit, [Err_general] can be used.

*)

(** If this is false, Sail will never generate any warnings *)
val opt_warnings : bool ref

(** How many backtrace entries to show for unreachable code errors *)
val opt_backtrace_length : int ref

(** {2 Auxiliary Functions } *)

(** [loc_to_string] prints a location as a string, including source code *)
val loc_to_string : Parse_ast.l -> string

(** [loc_file] returns the file for a location *)
val loc_file : Parse_ast.l -> string option

(** Reduce a location to a pair of positions if possible *)
val simp_loc : Ast.l -> (Lexing.position * Lexing.position) option

(** [short_loc_to_string] prints the location as a single line in a simple format *)
val short_loc_to_string : Parse_ast.l -> string

(** [print_err] prints a custom error message to stderr. *)
val print_err : Parse_ast.l -> string -> string -> unit

(** Reduce all spans in a location to just their starting characters *)
val start_loc : Parse_ast.l -> Parse_ast.l

(** {2 The error type } *)

(** Errors stop execution and print a message; they typically have a location and message.

Note that all these errors are intended to be fatal, so should not be caught other than by the top-level function.
*)
type error = private
  | Err_general of Parse_ast.l * string  (** General errors, used for multi purpose. If you are unsure, use this one. *)
  | Err_unreachable of Parse_ast.l * (string * int * int * int) * Printexc.raw_backtrace * string
      (** Unreachable errors should never be thrown. They represent an internal Sail error. *)
  | Err_todo of Parse_ast.l * string  (** [Err_todo] indicates that some feature is unimplemented. *)
  | Err_syntax of Lexing.position * string
  | Err_syntax_loc of Parse_ast.l * string
      (** [Err_syntax] and [Err_syntax_loc] are used for syntax errors by the parser. *)
  | Err_lex of Lexing.position * string  (** [Err_lex] is a lexical error generated by the lexer. *)
  | Err_type of Parse_ast.l * string option * string  (** [Err_type] is a type error. See the Type_error module. *)

exception Fatal_error of error

val err_todo : Parse_ast.l -> string -> exn
val err_general : Parse_ast.l -> string -> exn
val err_unreachable : Parse_ast.l -> string * int * int * int -> string -> exn
val err_typ : ?hint:string -> Parse_ast.l -> string -> exn
val err_syntax : Lexing.position -> string -> exn
val err_syntax_loc : Parse_ast.l -> string -> exn
val err_lex : Lexing.position -> string -> exn

(** Raise an unreachable exception.

This should always be used over an assert false or a generic OCaml failwith exception when appropriate *)
val unreachable : Parse_ast.l -> string * int * int * int -> string -> 'a

(** Print an error to stdout.

@param interactive If this is true (default false) then unreachable errors are reported as general errors. 
This is used by the interactive read-eval-print loop. The interactive mode exposes a lot of internal features, so
it's possible to excute code paths from the interactive mode that would otherwise be unreachable during normal execution. *)
val print_error : ?interactive:bool -> error -> unit

(** This function transforms all errors raised by the provided function into internal [Err_unreachable] errors *)
val forbid_errors : string * int * int * int -> ('a -> 'b) -> 'a -> 'b

(** Print a warning message. The first string is printed before the
   location, the second after. *)
val warn : ?once_from:string * int * int * int -> string -> Parse_ast.l -> string -> unit

val format_warn : ?once_from:string * int * int * int -> string -> Parse_ast.l -> Error_format.message -> unit

(** Print a simple one-line warning without a location. *)
val simple_warn : string -> unit

(** Will suppress all warnings for a given (Sail) file name. Used by
   $suppress_warnings directive in process_file.ml *)
val suppress_warnings_for_file : string -> unit

val get_sail_dir : string -> string

(** Run a command using Unix.system, but raise a Reporting exception if the command fails or is stopped/killed by a signal *)
val system_checked : ?loc:Parse_ast.l -> string -> unit
