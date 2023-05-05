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
open Ast_util
open Util
open Type_check

(*Determines if the first typ is within the range of the the second typ,
  using the constraints provided when the first typ contains variables.
  It is an error for second typ to be anything other than a range type
  If the first typ is a vector, then determines if the max representable
  number is in the range of the second; it is an error for the first typ
  to be anything other than a vector, a range, an atom, or a bit (after
  suitable unwrapping of abbreviations, reg, and registers).
*)
(* val is_within_range: typ -> typ -> nexp_range list -> triple
   val is_within_machine64 : typ -> nexp_range list -> triple *)

(* free variables and dependencies *)

(*fv_of_def consider_ty_vars consider_scatter_as_one all_defs all_defs def -> (bound_by_def, free_in_def) *)
(* val fv_of_def: bool -> bool -> ('a def) list -> 'a def -> Nameset.t * Nameset.t *)

(*group_defs consider_scatter_as_one all_defs -> ((bound_by_def, free_in_def), def) list *)
(* val group_defs : bool -> 'a defs -> ((Nameset.t * Nameset.t) * ('a def)) list *)

(*reodering definitions, initial functions *)
(* produce a new ordering for defs, limiting to those listed in the list, which respects dependencies *)
(* val restrict_defs : 'a defs -> string list -> 'a defs *)

val top_sort_defs : tannot ast -> tannot ast

(** Return the set of mutable variables assigned to in the given AST. *)
val assigned_vars : 'a exp -> IdSet.t

val assigned_vars_in_fexps : 'a fexp list -> IdSet.t
val assigned_vars_in_pexp : 'a pexp -> IdSet.t
val assigned_vars_in_lexp : 'a lexp -> IdSet.t

(** Variable bindings in patterns and expressions *)
val pat_id_is_variable : env -> id -> bool

val bindings_from_pat : tannot pat -> id list
val bound_vars : 'a exp -> IdSet.t

val equal_kids_ncs : kid -> n_constraint list -> KidSet.t
val equal_kids : env -> kid -> KidSet.t

(** Type-level substitutions into patterns and expressions.  Also attempts to
    update type annotations, but not the associated environments. *)
val nexp_subst_pat : nexp KBindings.t -> tannot pat -> tannot pat

val nexp_subst_exp : nexp KBindings.t -> tannot exp -> tannot exp
