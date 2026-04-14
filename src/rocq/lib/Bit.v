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

From Stdlib Require Import BinNums.

From stdpp Require Import base.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import bitvector.tactics.
From stdpp Require Import list.

From Sail Require Import BvUtil.

Inductive bit : Set :=
  | B0 : bit
  | B1 : bit.

Definition bit_eqb (lhs rhs : bit) : bool :=
  match (lhs, rhs) with
  | (B0, B0) => true
  | (B1, B1) => true
  | _ => false
  end.

Definition bit_to_bool (b : bit) : bool :=
  match b with
  | B0 => false
  | B1 => true
  end.

Definition bool_to_bit (b : bool) : bit :=
  match b with
  | false => B0
  | true => B1
  end.

Lemma bit_eqb_refl : ∀ b, bit_eqb b b = true.
Proof.
  destruct b; reflexivity.
Qed.

Lemma bit_eqb_comm : ∀ {x y}, bit_eqb x y = bit_eqb y x.
Proof. intros x y; destruct x, y; reflexivity. Qed.

Module Bits.
  Definition t : Set := list bit.

  Definition to_bv (x : list bit) : bv (N.of_nat (length x)) :=
    bv_cast (f_equal N.of_nat (length_map bit_to_bool x)) (BoolList.to_bv (List.map bit_to_bool x)).

  Definition to_bvn (x : list bit) : bvn := BoolList.to_bv (List.map bit_to_bool x).
End Bits.

Module Three.
  Inductive ubit : Set :=
    | B0 : ubit
    | B1 : ubit
    | BU : ubit.

  Module Notations.
    Notation "0" := B0.
    Notation "1" := B1.
    Notation "?" := BU.
  End Notations.

  Import Notations.

  Definition from_bool (b : bool) : ubit :=
    if b then 1 else 0.

  Definition from_bit (b : bit) : ubit :=
    match b with
    | Bit.B0 => 0
    | Bit.B1 => 1
    end.

  Definition bit_not (b : ubit) : ubit :=
    match b with
    | 0 => 1
    | 1 => 0
    | ? => ?
    end.

  Definition bit_or (lhs rhs : ubit) : ubit :=
    match (lhs, rhs) with
    | (0, 0) => 0
    | (0, 1) => 1
    | (0, ?) => ?
    | (1, 0) => 1
    | (1, 1) => 1
    | (1, ?) => 1
    | (?, 0) => ?
    | (?, 1) => 1
    | (?, ?) => ?
    end.

  Lemma bit_or_comm : ∀ (x y : ubit), bit_or x y = bit_or y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Lemma bit_or_assoc : ∀ x y z, bit_or x (bit_or y z) = bit_or (bit_or x y) z.
  Proof. intros x y z; destruct x, y, z; reflexivity. Qed.

  Definition bit_and (lhs rhs : ubit) : ubit :=
    match (lhs, rhs) with
    | (0, 0) => 0
    | (0, 1) => 0
    | (0, ?) => 0
    | (1, 0) => 0
    | (1, 1) => 1
    | (1, ?) => ?
    | (?, 0) => 0
    | (?, 1) => ?
    | (?, ?) => ?
    end.

  Lemma bit_and_comm : ∀ (x y : ubit), bit_and x y = bit_and y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Lemma bit_and_assoc : ∀ x y z, bit_and x (bit_and y z) = bit_and (bit_and x y) z.
  Proof. intros x y z; destruct x, y, z; reflexivity. Qed.

  Lemma de_morgan_not_or : ∀ x y, bit_not (bit_or x y) = bit_and (bit_not x) (bit_not y).
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Lemma de_morgan_not_and : ∀ x y, bit_not (bit_and x y) = bit_or (bit_not x) (bit_not y).
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Definition bit_xor (lhs rhs : ubit) : ubit :=
    match (lhs, rhs) with
    | (0, 0) => 0
    | (0, 1) => 1
    | (0, ?) => ?
    | (1, 0) => 1
    | (1, 1) => 0
    | (1, ?) => ?
    | (?, 0) => ?
    | (?, 1) => ?
    | (?, ?) => ?
    end.

  Lemma bit_xor_comm : ∀ (x y : ubit), bit_xor x y = bit_xor y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Lemma bit_xor_assoc : ∀ x y z, bit_xor x (bit_xor y z) = bit_xor (bit_xor x y) z.
  Proof. intros x y z; destruct x, y, z; reflexivity. Qed.

  Lemma bit_xor_alt: ∀ (x y : ubit),
    bit_or (bit_and (bit_not x) y) (bit_and x (bit_not y)) = bit_xor x y.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Definition bit_add (lhs rhs : ubit) : ubit * ubit :=
    match (lhs, rhs) with
    | (0, 0) => (0, 0)
    | (0, 1) => (1, 0)
    | (0, ?) => (?, 0)
    | (1, 0) => (1, 0)
    | (1, 1) => (0, 1)
    | (1, ?) => (?, ?)
    | (?, 0) => (?, 0)
    | (?, 1) => (?, ?)
    | (?, ?) => (?, ?)
    end.

  Lemma bit_add_comm : ∀ (x y : ubit), bit_add x y = bit_add y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Definition bit_join (x y : ubit) : ubit :=
    match (x, y) with
    | (0, 0) => 0
    | (1, 1) => 1
    | _  => ?
    end.

  Lemma bit_join_comm : ∀ (x y : ubit), bit_join x y = bit_join y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Lemma bit_join_assoc: ∀ x y z, bit_join x (bit_join y z) = bit_join (bit_join x y) z.
  Proof. intros x y z; destruct x, y, z; reflexivity. Qed.

  Definition bit_meet (x y : ubit) : option ubit :=
    match (x, y) with
    | (0, 0) => Some 0
    | (0, ?) => Some 0
    | (?, 0) => Some 0
    | (1, 1) => Some 1
    | (1, ?) => Some 1
    | (?, 1) => Some 1
    | (?, ?) => Some ?
    | _ => None
    end.

  Lemma bit_meet_comm : ∀ (x y : ubit), bit_meet x y = bit_meet y x.
  Proof. intros x y; destruct x, y; reflexivity. Qed.

  Definition bit_leb (x y : ubit) : bool :=
    match (x, y) with
    | (0, 0) => true
    | (1, 1) => true
    | (_, ?) => true
    | _ => false
    end.
End Three.
