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
From Sail Require Import Tactics.

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

  Definition to_bool (u : bool) (b : ubit) : bool :=
    match b with
    | 0 => false
    | 1 => true
    | ? => u
    end.

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

  Definition bit_add_carry (lhs rhs carry : ubit) : ubit * ubit :=
    match (lhs, rhs, carry) with
    | (0, 0, 0) => (0, 0)
    | (0, 0, 1) => (1, 0)
    | (0, 0, ?) => (?, 0)
    | (0, 1, 0) => (1, 0)
    | (0, 1, 1) => (0, 1)
    | (0, 1, ?) => (?, ?)
    | (0, ?, 0) => (?, 0)
    | (0, ?, 1) => (?, ?)
    | (0, ?, ?) => (?, ?)
    | (1, 0, 0) => (1, 0)
    | (1, 0, 1) => (0, 1)
    | (1, 0, ?) => (?, ?)
    | (1, 1, 0) => (0, 1)
    | (1, 1, 1) => (1, 1)
    | (1, 1, ?) => (?, ?)
    | (1, ?, 0) => (?, ?)
    | (1, ?, 1) => (?, ?)
    | (1, ?, ?) => (?, ?)
    | (?, 0, 0) => (?, 0)
    | (?, 0, 1) => (?, ?)
    | (?, 0, ?) => (?, ?)
    | (?, 1, 0) => (?, ?)
    | (?, 1, 1) => (?, ?)
    | (?, 1, ?) => (?, ?)
    | (?, ?, 0) => (?, ?)
    | (?, ?, 1) => (?, ?)
    | (?, ?, ?) => (?, ?)
    end.

  Lemma bit_add_carry_0 : ∀ x y, bit_add_carry x y 0 = bit_add x y.
  Proof. destruct x, y; reflexivity. Qed.

  Lemma bit_add_carry_0_r : ∀ x c, bit_add_carry x 0 c = bit_add x c.
  Proof. destruct x, c; reflexivity. Qed.

  Lemma bit_add_carry_0_l : ∀ y c, bit_add_carry 0 y c = bit_add y c.
  Proof. destruct y, c; reflexivity. Qed.

  Fixpoint bitlist_add_carry_acc (xs ys : list ubit) (c : ubit) (zs : list ubit) : list ubit * ubit :=
    match xs with
    | [] => (zs, c)
    | x :: xs =>
        match ys with
        | [] =>
            let '(z, c) := bit_add x c in
            bitlist_add_carry_acc xs ys c (z :: zs)
        | y :: ys =>
            let '(z, c) := bit_add_carry x y c in
            bitlist_add_carry_acc xs ys c (z :: zs)
        end
    end.

  Definition bitlist_add_carry (xs ys : list ubit) : list ubit * ubit :=
    bitlist_add_carry_acc (rev xs) (rev ys) 0 [].

  Lemma length_bitlist_add_carry_acc : ∀ xs ys c zs, length (fst (bitlist_add_carry_acc xs ys c zs)) = length xs + length zs.
  Proof.
    intros xs.
    induction xs as [| x xs IH]; intros ys c zs.
    - reflexivity.
    - destruct ys as [| y ys]; cbn [bitlist_add_carry_acc]; destruct_match; rewrite IH; cbn; lia.
  Qed.

  Lemma length_bitlist_add_carry : ∀ xs ys, length (fst (bitlist_add_carry xs ys)) = length xs.
  Proof. intros. unfold bitlist_add_carry. rewrite length_bitlist_add_carry_acc. simp_length. Qed.

  Hint Rewrite length_bitlist_add_carry_acc : length_db.
  Hint Rewrite length_bitlist_add_carry : length_db.

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

  Definition bitwise_op_correct_1 (bit_op : ubit → ubit → ubit) (bool_op : bool → bool → bool) : Prop :=
    ∀ x y, bit_op (from_bool x) (from_bool y) = from_bool (bool_op x y).

  Definition bitwise_op_correct_2 (bv_op : ∀ n, bv n → bv n → bv n) (bit_op : ubit → ubit → ubit) : Prop :=
    ∀ n x y,
      map from_bool (bv_to_bits (bv_op n x y))
      = zip_with bit_op (map from_bool (bv_to_bits x)) (map from_bool (bv_to_bits y)).

  Definition bitwise_op_correct
    (bv_op : ∀ n, bv n → bv n → bv n) (bit_op : ubit → ubit → ubit) (bool_op : bool → bool → bool) : Prop
    := bitwise_op_correct_1 bit_op bool_op ∧ bitwise_op_correct_2 bv_op bit_op.

  Lemma list_lookup_map : ∀ {f : bool → ubit} {xs : list bool} {i : nat}, map f xs !! i = option_map f (xs !! i).
  Proof.
    intros f xs i.
    pose proof (list_lookup_fmap f xs i).
    unfold fmap, option_fmap in H.
    rewrite <- H.
    reflexivity.
  Qed.

  Lemma option_map_from_bool_Some : ∀ {A B} {f: A → B} {x y}, option_map f x = Some y → ∃b, x = Some b ∧ y = f b.
  Proof.
    intros ??? x y H. destruct x as [x |]; [| discriminate].
    exists x.
    split.
    - reflexivity.
    - cbn in H. apply Some_inj in H. subst.
      reflexivity.
  Qed.

  Lemma bit_and_from_bool : ∀ x y, bit_and (from_bool x) (from_bool y) = from_bool (andb x y).
  Proof. destruct x, y; reflexivity. Qed.

  Ltac prove_bitwise_op_correct :=
    lazymatch goal with
    | |- bitwise_op_correct _ _ _ =>
        unfold bitwise_op_correct;
        apply and_wlog_r; [
          unfold bitwise_op_correct_1; intros;
          repeat (lazymatch goal with [ b : bool |- _ ] => destruct b end);
          reflexivity
        | let H := fresh "H" in
          intros H;
          let n := fresh "n" in
          unfold bitwise_op_correct_2; intros n ? ?;
          apply (list_eq_same_length _ _ (N.to_nat n)); [ simp_length | simp_length |];
          let L := fresh "L" in
          let R := fresh "R" in
          intros ? ? ? ? L R;
          rewrite lookup_zip_with_Some in R;
          destruct R as [? [? (? & ? & ?)]];
          repeat (
            lazymatch goal with
            | [ H : map from_bool (bv_to_bits _) !! _ = Some _ |- _ ] =>
                rewrite list_lookup_map in H;
                apply option_map_from_bool_Some in H;
                destruct H as [? [? ?]]
            end
          );
          repeat (
            lazymatch goal with
            | [ H : bv_to_bits _ !! _ = Some _ |- _ ] =>
                rewrite bv_to_bits_lookup_Some in H; destruct H as [_ ?]
            end
          );
          subst;
          unfold bitwise_op_correct_1 in H; rewrite H;
          f_equal; bv_simplify; clear
        ]
    end.

  Lemma and_correct : bitwise_op_correct (@bv_and) bit_and andb.
  Proof. prove_bitwise_op_correct. rewrite Z.land_spec. reflexivity. Qed.

  Lemma or_correct : bitwise_op_correct (@bv_or) bit_or orb.
  Proof. prove_bitwise_op_correct. rewrite Z.lor_spec. reflexivity. Qed.

  Lemma xor_correct : bitwise_op_correct (@bv_xor) bit_xor xorb.
  Proof. prove_bitwise_op_correct. rewrite Z.lxor_spec. reflexivity. Qed.

  Lemma bit_not_from_bool : ∀ {b}, bit_not (from_bool b) = from_bool (negb b).
  Proof. intros b. destruct b; reflexivity. Qed.
End Three.
