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

Require Extraction.

From Stdlib Require Import String.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.

From Ltac2 Require Import Ltac2.

From stdpp Require Import base.
From stdpp Require Import countable.
From stdpp Require Import strings.

(** Export Ltac2, so we can use Ltac2 as the default language for
defining tactics, without having to reset the default proof mode after
importing from Ltac2. *)
Export Ltac2.

#[export] Set Default Proof Mode "Classic".

(** The stdpp [Countable] instance is unusable for extracted code, and
we can't override it because the functions that encode and decode
strings are declared as local.

As a workaround, declare an [extstring] wrapper, with encode/decode
functions that extract directly to OCaml functions. *)

Inductive extstring :=
  | Extstring : string → extstring.

Extract Inductive extstring => "string" [ "" ].

Definition extstring_encode (str : extstring) := let 'Extstring str := str in encode str.
Definition extstring_decode (p : positive) := Extstring <$> decode p.

Extract Constant extstring_encode => "Extr_util.String_encoding.encode".
Extract Constant extstring_decode => "Extr_util.String_encoding.decode".

Lemma extstring_decode_encode : ∀ str, extstring_decode (extstring_encode str) = Some str.
Proof.
  intros str. destruct str.
  unfold extstring_decode. cbn. rewrite decode_encode.
  reflexivity.
Qed.

#[global]
Instance extstring_eqdec : EqDecision extstring.
Proof.
  intros x y. destruct x as [x]. destruct y as [y].
  unfold Decision.
  destruct (decide (x = y)) as [Eq | Neq].
  - left. rewrite Eq. reflexivity.
  - right. intros H. inversion H. done.
Defined.

#[global]
Instance extstring_countable : Countable extstring := {|
  encode := extstring_encode;
  decode := extstring_decode;
  decode_encode := extstring_decode_encode;
|}.

(** Declare a notation scope for this development. *)

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
