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

(** Initial desugaring pass over AST after parsing *)

open Ast
open Ast_defs
open Ast_util

(** {2 Options} *)

(** If enabled, bitvector types are only well-formed if their arguments are natural numbers. *)
val opt_strict_bitvector : bool ref

(** Generate faster undefined_T functions. Rather than generating functions that allow for the undefined values of enums
    and variants to be picked at runtime using a RNG or similar, this creates undefined_T functions for those types that
    simply return a specific member of the type chosen at compile time, which is much faster. These functions don't have
    the right effects, so the -no_effects flag may be needed if this is true. False by default. *)
val opt_fast_undefined : bool ref

(** Allow parsing internal constructs that should otherwise not appear in regular code *)
val opt_allow_internal : bool ref

(** {2 Contexts} *)

type ctx

val merge_ctx : Parse_ast.l -> ctx -> ctx -> ctx

val initial_ctx : ctx

(** {2 Desugar and process AST} *)

val to_ast_typ_arg : kind_aux -> ctx -> Parse_ast.atyp -> typ_arg

val get_uninitialized_registers : untyped_def list -> (id * typ) list

val generate_undefined_record_context : typquant -> (id * typ) list

val generate_undefined_record : id -> typquant -> ((id * typ) * unit def_annot) list -> untyped_def list

val generate_undefined_enum : id -> id list -> untyped_def list

(** Val specs of undefined functions for builtin types that get added to the AST by generate_undefinds (minus those
    functions that already exist in the AST). *)
val undefined_builtin_val_specs : unit -> untyped_def list

val generate_undefineds : IdSet.t -> untyped_def list

val generate_initialize_registers : IdSet.t -> (id * typ) list -> untyped_def list

val generate_enum_number_conversions : untyped_def list -> untyped_def list

val generate : untyped_ast -> untyped_ast

val process_ast : ctx -> Parse_ast.defs -> untyped_ast * ctx

(** {2 Constructing notation attributes} *)
val notation_attr : Parse_ast.l -> int -> string list -> uannot -> uannot

(** {2 Parsing expressions and definitions from strings} *)

val hex_digit_of_char : char -> (hex_digit * digit_case option) option

val parse_hex_lit : ?warn_inconsistent_case:Parse_ast.l -> string -> hex_digit non_empty list option
val parse_bin_lit : string -> bin_digit non_empty list option

val extern_of_string : ?pure:bool -> id -> string -> untyped_def

val val_spec_of_string : id -> string -> untyped_def

val defs_of_string : string * int * int * int -> ctx -> string -> untyped_def list * ctx

val ast_of_def_string : ?inline:Lexing.position -> string * int * int * int -> ctx -> string -> untyped_ast * ctx

val ast_of_def_string_with :
  ?inline:Lexing.position ->
  string * int * int * int ->
  ctx ->
  (Parse_ast.def list -> Parse_ast.def list) ->
  string ->
  untyped_ast * ctx

val exp_of_string : ?inline:Lexing.position -> string -> uannot exp

val typ_of_string : ?inline:Lexing.position -> string -> typ

val constraint_of_string : ?inline:Lexing.position -> string -> n_constraint

val parse_from_string : (Lexing.lexbuf -> 'a) -> ?inline:Lexing.position -> string -> 'a

(** {2 Parsing files} *)

(** Parse a file into a sequence of comments and a parse AST

    @param ?loc If we get an error reading the file, report the error at this location *)
val parse_file : ?loc:Parse_ast.l -> string -> Lexer.comment list * Parse_ast.def list

val get_lexbuf_from_string : filename:string -> contents:string -> Lexing.lexbuf

val parse_file_from_string : filename:string -> contents:string -> Lexer.comment list * Parse_ast.def list

val parse_project :
  ?inline:Lexing.position -> ?filename:string -> contents:string -> unit -> Project.def Project.spanned list
