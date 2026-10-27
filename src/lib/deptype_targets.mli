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

(* Helper functions intended for backends targetting shallow embeddings in dependently typed languages.

   In particular, these backends output bitvector types with arbitrary sizes, and these functions
   support producing dependent types when size information needs to be stored alongside a value
   because a bitvector is inside an existential Sail type (e.g., {'n, 'n > 0. (int('n), bits('n))}).

   The general scheme for these sizes is that the local context provides enough information for them
   within definitions and the existentially bound type variables don't need to appear, but dependent
   pairs are generated when a value is communicated elsewhere (e.g., a function argument or return
   value) or embedded in a datatype or tuple and its Sail type has some existentially bound size
   information.
 *)

open Ast
open Ast_compare

(* Sometimes we need to print a type in a position where any existential has already been stripped
   out.  Where the existential variables should appear we attempt to get a concrete value by
   unification with another type (e.g., in a let binding), and otherwise use _ and hope that Rocq
   can figure it out.
 *)

val unfold_exists_typ : (string lazy_t -> unit) -> Type_check.env -> ?instantiated_type:typ -> typ -> KidSet.t * typ

(* Returns the set of type variables that will appear in the target's output, which may be smaller
   than those in the Sail type because we keep bitvector sizes but drop integer types. *)

val tyvars_of_typ : typ -> KidSet.t

(* Calculate the existential type bindings that should make it into the Rocq output as dependent pairs. *)

(* Takes the components of an existential type as arguments, except for the constraint *)
val relevant_existential_vars : Type_check.env -> kinded_id list -> typ -> kinded_id list * typ

(* Takes any type *)
val relevant_type_vars : Type_check.env -> typ -> kinded_id list * typ

(* [typ_of_constructor env id typ l] provides the argument type for a constructor [id], with any
   parameters of the data type filled in by unification against [typ]. *)
val typ_of_constructor : Type_check.env -> id -> typ -> l -> typ
