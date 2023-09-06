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

(** Initial desugaring pass over AST after parsing *)

open Ast
open Ast_defs
open Ast_util

type ctx

val merge_ctx : Parse_ast.l -> ctx -> ctx -> ctx

(** {2 Options} *)

(** Generate undefined_T functions for every type T. False by
   default. *)
val opt_undefined_gen : bool ref

(** Generate faster undefined_T functions. Rather than generating
   functions that allow for the undefined values of enums and variants
   to be picked at runtime using a RNG or similar, this creates
   undefined_T functions for those types that simply return a specific
   member of the type chosen at compile time, which is much
   faster. These functions don't have the right effects, so the
   -no_effects flag may be needed if this is true. False by
   default. *)
val opt_fast_undefined : bool ref

(** Allow # in identifiers when set, much like the GHC option of the same
   name *)
val opt_magic_hash : bool ref

(** This is a bit of a hack right now - it ensures that the undefiend
   builtins (undefined_vector etc), only get added to the AST
   once. The original assumption in sail is that the whole AST gets
   processed at once (therefore they could only get added once), and
   this isn't true any more with the interpreter. This needs to be
   public so the interpreter can set it back to false if it unloads
   all the loaded files. *)
val have_undefined_builtins : bool ref

(** Val specs of undefined functions for builtin types that get added to
    the AST if opt_undefined_gen is set (minus those functions that already
    exist in the AST). *)
val undefined_builtin_val_specs : uannot def list

(** {2 Desugar and process AST } *)

val generate_undefineds : IdSet.t -> uannot def list -> uannot def list
val generate_enum_functions : IdSet.t -> uannot def list -> uannot def list

(** If the generate flag is false, then we won't generate any
   auxilliary definitions, like the initialize_registers function *)
val process_ast : ?generate:bool -> Parse_ast.defs -> uannot ast

(** {2 Parsing expressions and definitions from strings} *)

val extern_of_string : ?pure:bool -> id -> string -> uannot def
val val_spec_of_string : id -> string -> uannot def
val defs_of_string : string * int * int * int -> string -> uannot def list
val ast_of_def_string : string * int * int * int -> string -> uannot ast
val ast_of_def_string_with :
  string * int * int * int -> (Parse_ast.def list -> Parse_ast.def list) -> string -> uannot ast
val exp_of_string : string -> uannot exp
val typ_of_string : string -> typ
val constraint_of_string : string -> n_constraint

(** {2 Parsing files } *)

(** Parse a file into a sequence of comments and a parse AST

   @param ?loc If we get an error reading the file, report the error at this location *)
val parse_file : ?loc:Parse_ast.l -> string -> Lexer.comment list * Parse_ast.def list

val parse_file_from_string : filename:string -> contents:string -> Lexer.comment list * Parse_ast.def list
