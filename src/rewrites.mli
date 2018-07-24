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

open Ast
open Type_check

(* Monomorphisation options *)
val opt_mono_rewrites : bool ref
val opt_mono_complex_nexps : bool ref
val opt_mono_split : ((string * int) * string) list ref
val opt_dmono_analysis : int ref
val opt_auto_mono : bool ref
val opt_dall_split_errors : bool ref
val opt_dmono_continue : bool ref

(* Generate a fresh id with the given prefix *)
val fresh_id : string -> l -> id

(* Re-write undefined to functions created by -undefined_gen flag *)
val rewrite_undefined : bool -> tannot defs -> tannot defs

(* Perform rewrites to exclude AST nodes not supported for ocaml out*)
val rewrite_defs_ocaml : (string * (tannot defs -> tannot defs)) list

(* Perform rewrites to exclude AST nodes not supported for interpreter *)
val rewrite_defs_interpreter : (string * (tannot defs -> tannot defs)) list

(* Perform rewrites to exclude AST nodes not supported for lem out*)
val rewrite_defs_lem : (string * (tannot defs -> tannot defs)) list

(* Perform rewrites to exclude AST nodes not supported for coq out*)
val rewrite_defs_coq : (string * (tannot defs -> tannot defs)) list

(* Warn about matches where we add a default case for Coq because they're not
   exhaustive *)
val opt_coq_warn_nonexhaustive : bool ref

(* Perform rewrites to exclude AST nodes not supported for C compilation *)
val rewrite_defs_c : (string * (tannot defs -> tannot defs)) list

(* This is a special rewriter pass that checks AST invariants without
   actually doing any re-writing *)
val rewrite_defs_check : (string * (tannot defs -> tannot defs)) list

val simple_typ : typ -> typ
