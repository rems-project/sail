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

val parse_file : string -> Parse_ast.defs
val convert_ast : Parse_ast.defs -> unit Ast.defs
val check_ast: unit Ast.defs -> Type_check.tannot Ast.defs * Type_check.Env.t
val monomorphise_ast : ((string * int) * string) list -> Type_check.tannot Ast.defs -> Type_check.tannot Ast.defs * Type_check.Env.t
val rewrite_ast: Type_check.tannot Ast.defs -> Type_check.tannot Ast.defs
val rewrite_ast_lem : Type_check.tannot Ast.defs -> Type_check.tannot Ast.defs
val rewrite_ast_ocaml : Type_check.tannot Ast.defs -> Type_check.tannot Ast.defs

val load_file : Type_check.Env.t -> string -> Type_check.tannot Ast.defs * Type_check.Env.t

val opt_new_typecheck : bool ref
val opt_just_check : bool ref
val opt_ddump_tc_ast : bool ref
val opt_dno_cast : bool ref

type out_type =
  | Lem_ast_out
  | Lem_out of string option (* If present, the string is a file to open in the lem backend*)
  | Ocaml_out of string option (* If present, the string is a file to open in the ocaml backend*)

val output :
  string ->                           (* The path to the library *)
  out_type ->                         (* Backend kind *)
  (string * Type_check.tannot Ast.defs) list -> (*File names paired with definitions *)
  unit

(** [always_replace_files] determines whether Sail only updates modified files.
    If it is set to [true], all output files are written, regardless of whether the
    files existed before. If it is set to [false] and an output file already exists,
    the output file is only updated, if its content really changes. *)
val always_replace_files : bool ref
