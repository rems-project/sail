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

open Ast
open Ast_defs
open Type_check

(* Monomorphisation options *)
val opt_mono_rewrites : bool ref
val opt_mono_complex_nexps : bool ref
val opt_mono_split : ((string * int) * string) list ref
val opt_dmono_analysis : int ref
val opt_auto_mono : bool ref
val opt_dall_split_errors : bool ref
val opt_dmono_continue : bool ref

(** Warn about matches where we add a default case for Coq because
   they're not exhaustive *)
val opt_coq_warn_nonexhaustive : bool ref

(** Output each rewrite step (as produced by the rewrite function) to
   a file for debugging *)
val opt_ddump_rewrite_ast : (string * int) option ref

(** Generate a fresh id with the given prefix *)
val fresh_id : string -> l -> id

(** Move loop termination measures into loop AST nodes *)
val move_loop_measures : 'a ast -> 'a ast

(** Re-write undefined to functions created by -undefined_gen flag *)
val rewrite_undefined : bool -> Env.t -> tannot ast -> tannot ast

type rewriter =
  | Base_rewriter of (Effects.side_effect_info -> Env.t -> tannot ast -> tannot ast * Effects.side_effect_info * Env.t)
  | Bool_rewriter of (bool -> rewriter)
  | String_rewriter of (string -> rewriter)
  | Literal_rewriter of ((lit -> bool) -> rewriter)

val describe_rewriter : rewriter -> string list

val all_rewriters : (string * rewriter) list

type rewrite_sequence =
  (string * (Effects.side_effect_info -> Env.t -> tannot ast -> tannot ast * Effects.side_effect_info * Env.t)) list

val rewrite_lit_ocaml : lit -> bool
val rewrite_lit_lem : lit -> bool

type rewriter_arg =
  | If_mono_arg
  | If_mwords_arg
  | If_flag of bool ref
  | Bool_arg of bool
  | Flag_arg of bool ref
  | String_arg of string
  | Literal_arg of string

(** Get the list of instantiated rewrites for a list of rewrites *)
val instantiate_rewrites : (string * rewriter_arg list) list -> rewrite_sequence

(** Apply a sequence of rewrites to an AST *)
val rewrite :
  Effects.side_effect_info -> Env.t -> rewrite_sequence -> tannot ast -> tannot ast * Effects.side_effect_info * Env.t

val rewrites_interpreter : (string * rewriter_arg list) list

val simple_typ : typ -> typ
