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

open Ast_defs

(** Parse a file. The optional loc argument is the location of the
   $include directive that is importing the file, if applicable. *)
val parse_file : ?loc:Parse_ast.l -> string -> Lexer.comment list * Parse_ast.def list

val clear_symbols : unit -> unit
val have_symbol : string -> bool
val add_symbol : string -> unit

val preprocess : string option -> (Arg.key * Arg.spec * Arg.doc) list -> Parse_ast.def list -> Parse_ast.def list
val check_ast : Type_check.Env.t -> unit ast -> Type_check.tannot ast * Type_check.Env.t * Effects.side_effect_info
val rewrite_ast_initial : Type_check.Env.t -> Type_check.tannot ast -> Type_check.tannot ast * Type_check.Env.t
val rewrite_ast_target : Effects.side_effect_info -> string -> Type_check.Env.t -> Type_check.tannot ast -> Type_check.tannot ast * Type_check.Env.t
val rewrite_ast_check : Type_check.Env.t -> Type_check.tannot ast -> Type_check.tannot ast * Type_check.Env.t

val opt_file_out : string option ref
val opt_memo_z3 : bool ref
val opt_just_check : bool ref
val opt_reformat : string option ref
val opt_ddump_initial_ast : bool ref
val opt_ddump_tc_ast : bool ref
val opt_ddump_rewrite_ast : ((string * int) option) ref
val opt_dno_cast : bool ref

val opt_lem_output_dir : (string option) ref
val opt_isa_output_dir : (string option) ref
val opt_coq_output_dir : (string option) ref
val opt_alt_modules_coq : (string list) ref
val opt_alt_modules2_coq : (string list) ref

type out_type =
  | Lem_out of string list (* If present, the strings are files to open in the lem backend*)
  | Coq_out of string list (* If present, the strings are files to open in the coq backend*)

val output :
  string -> (* The path to the library *)
  out_type -> (* Backend kind *)
  (string * Type_check.Env.t * Type_check.tannot ast) list -> (*File names paired with definitions *)
  unit

(** [always_replace_files] determines whether Sail only updates modified files.
    If it is set to [true], all output files are written, regardless of whether the
    files existed before. If it is set to [false] and an output file already exists,
    the output file is only updated, if its content really changes. *)
val always_replace_files : bool ref

val load_files : ?check:bool -> string option -> (Arg.key * Arg.spec * Arg.doc) list -> Type_check.Env.t -> string list -> (string * Type_check.tannot ast * Type_check.Env.t * Effects.side_effect_info)

val descatter : Type_check.Env.t -> Type_check.tannot ast -> Type_check.tannot ast * Type_check.Env.t
