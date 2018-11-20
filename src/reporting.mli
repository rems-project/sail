(**************************************************************************)
(*     Sail                                                               *)
(*                                                                        *)
(*  Copyright (c) 2013-2017                                               *)
(*    Kathyrn Gray                                                        *)
(*    Shaked Flur                                                         *)
(*    Stephen Kell                                                        *)
(*    Gabriel Kerneis                                                     *)
(*    Robert Norton-Wright                                                *)
(*    Christopher Pulte                                                   *)
(*    Peter Sewell                                                        *)
(*    Alasdair Armstrong                                                  *)
(*    Brian Campbell                                                      *)
(*    Thomas Bauereiss                                                    *)
(*    Anthony Fox                                                         *)
(*    Jon French                                                          *)
(*    Dominic Mulligan                                                    *)
(*    Stephen Kell                                                        *)
(*    Mark Wassell                                                        *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(**************************************************************************)

(** Basic error reporting

  [Reporting] contains functions to report errors and warnings. 
  It contains functions to print locations ([Parse_ast.l] and [Ast.l]) and lexing positions.

  The main functionality is reporting errors. This is done by raising a
  [Fatal_error] exception. This is caught internally and reported via [report_error]. 
  There are several predefined types of errors which all cause different error
  messages. If none of these fit, [Err_general] can be used.       

*)

(** {2 Auxiliary Functions } *)

(** [loc_to_string] includes code from file if code optional argument is true (default) *)
val loc_to_string : ?code:bool -> Parse_ast.l -> string

(** [print_err fatal print_loc_source l head mes] prints an error / warning message to
    std-err. It starts with printing location information stored in [l]
    It then prints "head: mes". If [fatal] is set, the program exists with error-code 1 afterwards.
*)
val print_err : bool -> bool -> Parse_ast.l -> string -> string -> unit

(** {2 Errors } *)

(** Errors stop execution and print a message; they typically have a location and message.
*)
type error = 
  (** General errors, used for multi purpose. If you are unsure, use this one. *)
  | Err_general of Parse_ast.l * string

  (** Unreachable errors should never be thrown. It means that some
      code was excuted that the programmer thought of as unreachable *)
  | Err_unreachable of Parse_ast.l * (string * int * int * int) * string

  (** [Err_todo] indicates that some feature is unimplemented; it should be built using [err_todo]. *)
  | Err_todo of Parse_ast.l * string

  | Err_syntax of Lexing.position * string
  | Err_syntax_locn of Parse_ast.l * string
  | Err_lex of Lexing.position * string
  | Err_type of Parse_ast.l * string
  | Err_type_dual of Parse_ast.l * Parse_ast.l * string
  
exception Fatal_error of error

(** [err_todo l m] is an abreviatiation for [Fatal_error (Err_todo (l, m))] *)
val err_todo : Parse_ast.l -> string -> exn

(** [err_general l m] is an abreviatiation for [Fatal_error (Err_general (b, l, m))] *)
val err_general : Parse_ast.l -> string -> exn

(** [err_unreachable l __POS__ m] is an abreviatiation for [Fatal_error (Err_unreachable (l, __POS__, m))] *)
val err_unreachable : Parse_ast.l -> (string * int * int * int) -> string -> exn

(** [err_typ l m] is an abreviatiation for [Fatal_error (Err_type (l, m))] *)
val err_typ : Parse_ast.l -> string -> exn

(** [err_typ_dual l1 l2 m] is an abreviatiation for [Fatal_error (Err_type_dual (l1, l2, m))] *)
val err_typ_dual : Parse_ast.l ->  Parse_ast.l -> string -> exn

(** Report error should only be used by main to print the error in the end. Everywhere else,
    raising a [Fatal_error] exception is recommended. *)
val report_error : error -> 'a

val print_error : error -> unit
