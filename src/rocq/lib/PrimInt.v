(* ************************************************************************ *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2026                                                 *)
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
(*  This work was partially supported by EPSRC grant EP/K008528/1 REMS:     *)
(*  Rigorous Engineering for Mainstream Systems, an ARM iCASE award, EPSRC  *)
(*  IAA KTF funding, and donations from Arm. This project has received      *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union's Horizon 2020 research and innovation programme (grant agreement *)
(*  No 789108, ELVER).                                                      *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  SPDX-License-Identifier: BSD-2-Clause                                   *)
(* ************************************************************************ *)

(** * Integer primitives

Concrete definitions of the Sail integer primitives, extracted to
OCaml to provide the implementations in [sail_lib.ml].

Sail integers are arbitrary precision, so they are represented by
[Z], which extraction maps onto Zarith's [Big_int_Z.big_int]/[Z.t]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.

Open Scope Z_scope.

Definition eq_int (x y : Z) : bool := Z.eqb x y.

Definition lt (x y : Z) : bool := Z.ltb x y.

Definition gt (x y : Z) : bool := Z.gtb x y.

Definition lteq (x y : Z) : bool := Z.leb x y.

Definition gteq (x y : Z) : bool := Z.geb x y.

(** ** Arithmetic operations *)

Definition add_int (x y : Z) : Z := x + y.

Definition sub_int (x y : Z) : Z := x - y.

Definition sub_nat (x y : Z) : Z := Z.max 0 (x - y).

Definition mult (x y : Z) : Z := (x * y).

Definition negate (x : Z) : Z := Z.opp x.

Definition abs_int (x : Z) : Z := Z.abs x.

Definition max_int (x y : Z) : Z := Z.max x y.

Definition min_int (x y : Z) : Z := Z.min x y.

(** ** Division

Sail has three division operators, defined in [lib/arith.sail] and
[lib/smt.sail].

- [tdiv_int] / [tmod_int] truncate towards zero, and bind to [tdiv_int] /
  [tmod_int] here (Rocq [Z.quot] / [Z.rem]).

- [ediv_int] / [emod_int] are Euclidean, and bind to [quotient] / [modulus]
  here. These are the definitions from the (unfortunately deprecated)
  [Stdlib.ZArith.Zeuclid] module, inlined in terms of the floor division of
  [BinInt].

- [fdiv_int] / [fmod_int] floor, and are defined in [lib/arith.sail] in terms of
  [tdiv_int], so they are not mentioned here. *)

Definition ediv_int (x y : Z) : Z := Z.sgn y * (x / Z.abs y).

Definition emod_int (x y : Z) : Z := x mod (Z.abs y).

(** The Euclidean division equation, and the fact that [modulus] is always
non-negative, which is what distinguishes this Euclidean div/mod from the floor
and truncating ones. *)

Lemma euclidian_div_mod : forall x y, y <> 0 -> x = y * ediv_int x y + emod_int x y.
Proof.
  intros x y Hy. unfold ediv_int, emod_int.
  rewrite Z.mul_assoc, Z.sgn_abs.
  apply Z.div_mod. now destruct y.
Qed.

Lemma euclidian_pos : forall x y, y <> 0 -> 0 <= emod_int x y < Z.abs y.
Proof.
  intros x y Hy. unfold emod_int.
  apply Z.mod_pos_bound. destruct y; compute; trivial. now destruct Hy.
Qed.

Definition tdiv_int (x y : Z) : Z := Z.quot x y.

Definition tmod_int (x y : Z) : Z := Z.rem x y.

Definition int_power (x y : Z) : Z := Z.pow x y.

Definition pow2 (x : Z) : Z := Z.pow 2 x.

Definition shl_int (n m : Z) : Z := Z.shiftl n m.

Definition shr_int (n m : Z) : Z := Z.shiftr n m.
