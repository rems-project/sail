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

(** Module for breaking AST into syntactic chunks and interleaving comments.

   This module is part of the Sail formatting system. It takes a
   parsed AST (not a desugared AST, as for formatting we need to
   preserve as much as possible), and breaks it up into more abstract
   syntactic elements - 'chunks' for want of a better term. *)

type binder = Var_binder | Let_binder | Internal_plet_binder

val binder_keyword : binder -> string

type if_format = { then_brace : bool; else_brace : bool }

type match_kind = Try_match | Match_match

val match_keywords : match_kind -> string * string option

val comment_type_delimiters : Lexer.comment_type -> string * string

type infix_chunk = Infix_prefix of string | Infix_op of string | Infix_chunks of chunks

and chunk =
  | Comment of Lexer.comment_type * int * int * string
  | Spacer of bool * int
  | Function of {
      id : Parse_ast.id;
      clause : bool;
      rec_opt : chunks option;
      typq_opt : chunks option;
      return_typ_opt : chunks option;
      funcls : (chunks * pexp_chunks) list;
    }
  | Val of { id : Parse_ast.id; extern_opt : Parse_ast.extern option; typq_opt : chunks option; typ : chunks }
  | Enum of { id : Parse_ast.id; enum_functions : chunks list option; members : chunks list }
  | Function_typ of { mapping : bool; lhs : chunks; rhs : chunks }
  | Exists of { vars : chunks; constr : chunks; typ : chunks }
  | Typ_quant of { vars : chunks; constr_opt : chunks option }
  | App of Parse_ast.id * chunks list
  | Field of chunks * Parse_ast.id
  | Tuple of string * string * int * chunks list
  | Intersperse of string * chunks list
  | Atom of string
  | String_literal of string
  | Pragma of string * string
  | Unary of string * chunks
  | Binary of chunks * string * chunks
  | Ternary of chunks * string * chunks * string * chunks
  | Infix_sequence of infix_chunk list
  | Index of chunks * chunks
  | Delim of string
  | Opt_delim of string
  | Block of (bool * chunks list)
  | Binder of binder * chunks * chunks * chunks
  | Block_binder of binder * chunks * chunks
  | If_then of bool * chunks * chunks
  | If_then_else of if_format * chunks * chunks * chunks
  | Struct_update of chunks * chunks list
  | Match of { kind : match_kind; exp : chunks; aligned : bool; cases : pexp_chunks list }
  | Foreach of {
      var : chunks;
      decreasing : bool;
      from_index : chunks;
      to_index : chunks;
      step : chunks option;
      body : chunks;
    }
  | While of { repeat_until : bool; termination_measure : chunks option; cond : chunks; body : chunks }
  | Vector_updates of chunks * chunk list
  | Chunks of chunks
  | Raw of string

and chunks = chunk Queue.t

and pexp_chunks = { funcl_space : bool; pat : chunks; guard : chunks option; body : chunks }

val prerr_chunk : string -> chunk -> unit

val chunk_defs : string -> Lexer.comment list -> Parse_ast.def list -> chunks
