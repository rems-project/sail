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

(** Basic error reporting

  [Reporting] contains functions to report errors and warnings.
  It contains functions to print locations ([Parse_ast.l] and [Ast.l]) and lexing positions.

  The main functionality is reporting errors. This is done by raising a
  [Fatal_error] exception. This is caught internally and reported via [report_error].
  There are several predefined types of errors which all cause different error
  messages. If none of these fit, [Err_general] can be used.

*)

val opt_warnings : bool ref

(** {2 Auxiliary Functions } *)

(** [loc_to_string] includes code from file if code optional argument is true (default) *)
val loc_to_string : ?code:bool -> Parse_ast.l -> string

(** [loc_file] returns the file for a location *)
val loc_file : Parse_ast.l -> string option
 
(** Reduce a location to a pair of positions if possible *)
val simp_loc : Ast.l -> (Lexing.position * Lexing.position) option

(** [short_loc_to_string] prints the location as a single line in a simple format *)
val short_loc_to_string : Parse_ast.l -> string

(** [print_err fatal print_loc_source l head mes] prints an error / warning message to
    std-err.
*)
val print_err : Parse_ast.l -> string -> string -> unit

(** {2 Errors } *)

(** Errors stop execution and print a message; they typically have a location and message.
*)
type error = private
  (** General errors, used for multi purpose. If you are unsure, use this one. *)
  | Err_general of Parse_ast.l * string

  (** Unreachable errors should never be thrown. It means that some
      code was excuted that the programmer thought of as unreachable *)
  | Err_unreachable of Parse_ast.l * (string * int * int * int) * Printexc.raw_backtrace * string

  (** [Err_todo] indicates that some feature is unimplemented; it should be built using [err_todo]. *)
  | Err_todo of Parse_ast.l * string

  | Err_syntax of Lexing.position * string
  | Err_syntax_loc of Parse_ast.l * string
  | Err_lex of Lexing.position * string
  | Err_type of Parse_ast.l * string

exception Fatal_error of error

val err_todo : Parse_ast.l -> string -> exn
val err_general : Parse_ast.l -> string -> exn
val err_unreachable : Parse_ast.l -> (string * int * int * int) -> string -> exn
val err_typ : Parse_ast.l -> string -> exn
val err_syntax : Lexing.position -> string -> exn
val err_syntax_loc : Parse_ast.l -> string -> exn
val err_lex : Lexing.position -> string -> exn

val unreachable : Parse_ast.l -> (string * int * int * int) -> string -> 'a

val print_error : error -> unit

val forbid_errors : (string * int * int * int) -> ('a -> 'b) -> 'a -> 'b
  
(** Print a warning message. The first string is printed before the
   location, the second after. *)
val warn : string -> Parse_ast.l -> string -> unit

(** Print a simple one-line warning without a location. *)
val simple_warn: string -> unit
  
(** Will suppress all warnings for a given file. Used by
   $suppress_warnings directive in process_file.ml *)
val suppress_warnings_for_file : string -> unit
