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

From Stdlib Require Import String.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.

From Ltac2 Require Import Ltac2.

From stdpp Require Import base.

(** Export Ltac2, so we can use Ltac2 as the default language for
defining tactics, without having to reset the default proof mode after
importing from Ltac2. *)
Export Ltac2.

#[export] Set Default Proof Mode "Classic".

Declare Scope sail_scope.
Delimit Scope sail_scope with sail.
#[global] Open Scope sail_scope.

Class EqDecb (A : Type) := {
  eqb : A → A → bool;
  eqb_true_iff : ∀ x y, eqb x y = true ↔ x = y
}.

Infix "==" := eqb (at level 70, no associativity) : sail_scope.

#[global] Instance nat_eqdecb : EqDecb nat := {
  eqb := Nat.eqb;
  eqb_true_iff := PeanoNat.Nat.eqb_eq
}.

#[global] Instance string_eqdecb : EqDecb string := {
  eqb := String.eqb;
  eqb_true_iff := String.eqb_eq
}.

#[global] Instance bool_eqdecb : EqDecb bool := {
  eqb := Bool.eqb;
  eqb_true_iff := Bool.eqb_true_iff
}.

Lemma Qc_eqb_true_iff : ∀ x y, Qeq_bool (this x) (this y) = true ↔ x = y.
Proof.
  split; intros H.
  - apply Qc_is_canon, Qeq_bool_iff, H.
  - subst. apply Qeq_bool_refl.
Qed.

#[global] Instance Qc_eqdecb : EqDecb Qc := {
  eqb := (fun x y => Qeq_bool (this x) (this y));
  eqb_true_iff := Qc_eqb_true_iff
}.

Lemma eqb_refl : ∀ {A} `{EqDecb A} (x : A), (x == x) = true.
Proof. intros ?? x. rewrite (eqb_true_iff x x). reflexivity. Qed.

Lemma eqb_false_iff : ∀ {A} `{EqDecb A} (x y : A), (x == y) = false ↔ x ≠ y.
Proof.
  intros ?? x y.
  split.
  - intros N xy.
    rewrite <- xy, (eqb_refl x) in N. discriminate.
  - intros N.
    destruct (x == y) eqn : E; try reflexivity.
    exfalso.
    rewrite eqb_true_iff in E.
    apply N in E.
    exact E.
Qed.

Ltac2 eqb_to_eq () :=
  repeat (
    lazy_match! goal with
    | [ h : context [ (?x == ?y) = true ] |- _ ] => rewrite (eqb_true_iff $x $y) in $h
    | [ h : context [ (?x == ?y) = false ] |- _ ] => rewrite (eqb_false_iff $x $y) in $h
    | [ |- context [ (?x == ?y) = true ] ] => rewrite (eqb_true_iff $x $y)
    | [ |- context [ (?x == ?y) = false ] ] => rewrite (eqb_false_iff $x $y)
    end
  ).

Ltac eqb_to_eq := ltac2:(eqb_to_eq ()).
