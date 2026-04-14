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

(** This file contains extra lemmas about stdpp bitvectors. *)

From stdpp Require Import base.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import bitvector.tactics.
From stdpp Require Import list.

From Sail Require Import Tactics.

Lemma bv_unsigned_log2 : ∀ {n} {x : bv n}, (0 < n)%N → (Z.log2 (bv_unsigned x) < Z.of_N n)%Z.
Proof.
  intros n x zero_lt_n.
  destruct x. unfold BvWf in bv_is_wf.
  unfold definitions.bv_unsigned.
  rewrite Is_true_true, andb_true_iff, Z.ltb_lt, Z.leb_le in bv_is_wf.
  unfold bv_modulus in bv_is_wf.
  destruct (bv_unsigned =? 0)%Z eqn : E.
  - rewrite Z.eqb_eq in E.
    rewrite E.
    cbn. lia.
  - apply Z.log2_lt_pow2.
    + lia.
    + apply (proj2 bv_is_wf).
Qed.

Lemma bv_unsigned_nonneg : ∀ {n} {x : bv n}, (0 ≤ bv_unsigned x)%Z.
Proof.
  intros n x.
  destruct x. unfold BvWf in bv_is_wf.
  unfold definitions.bv_unsigned.
  rewrite Is_true_true, andb_true_iff, Z.leb_le in bv_is_wf.
  easy.
Qed.

Lemma bv_unsigned_shiftl_nonneg : ∀ {n shift} {x : bv n}, (0 ≤ bv_unsigned x ≪ shift)%Z.
Proof.
  intros n m x.
  apply Z.shiftl_nonneg, bv_unsigned_nonneg.
Qed.

(** We want to show that [bv_to_bits] applied to [bv_concat] can be
simplified to a list append. This is to let us relate stdpp bitvectors
and bitlist style bitvectors.

First, we show it for non-empty bitvectors. *)

Lemma bv_concat_app_non_empty : ∀ {n m} {x : bv n} {y : bv m},
  (0 < n)%N →
  (0 < m)%N →
  bv_to_bits (bv_concat (n + m) x y) = bv_to_bits y ++ bv_to_bits x.
Proof.
  intros n m x y zero_lt_n zero_lt_m.
  apply (list_eq_same_length _ _ (N.to_nat (n + m))).
  - rewrite length_app. repeat rewrite length_bv_to_bits. lia.
  - rewrite length_bv_to_bits. reflexivity.
  - intros i lb rb i_lt_n_plus_m L R.
    rewrite bv_to_bits_lookup_Some in L. destruct L as [_ L].
    rewrite bv_concat_unsigned', bv_wrap_land in L.
    rewrite Z.land_ones_low in L; [| shelve | shelve ].
    rewrite lookup_app_Some in R.
    repeat rewrite bv_to_bits_lookup_Some in R.
    rewrite length_bv_to_bits in R.
    destruct R as [[i_lt_m Ry] | [? [? Rx]]]; subst.
    + rewrite Z.lor_spec, Z.shiftl_spec_low; [ reflexivity | lia ].
    + rewrite Z.lor_spec, Z.shiftl_spec_high; try lia.
      destruct (bv_unsigned y =? 0)%Z eqn : y_zero;
        [ rewrite Z.eqb_eq in y_zero | rewrite Z.eqb_neq in y_zero].
      * rewrite y_zero, Z.testbit_0_l, orb_false_r.
        f_equal. lia.
      * pattern (Z.testbit (bv_unsigned y) (Z.of_nat i)).
        rewrite Z.bits_above_log2, orb_false_r; [ f_equal; lia | apply bv_unsigned_nonneg |].
        apply (Z.lt_le_trans _ _ _ (bv_unsigned_log2 zero_lt_m)). lia.
    Unshelve.
    { apply Z.lor_nonneg; split; [ apply bv_unsigned_shiftl_nonneg | apply bv_unsigned_nonneg ]. }
    { rewrite Z.log2_lor.
      - apply Z.max_lub_lt.
        + destruct (bv_unsigned x =? 0)%Z eqn : x_zero. rewrite Z.eqb_eq in x_zero.
          * rewrite x_zero, Z.shiftl_0_l. cbn. lia.
          * rewrite Z.log2_shiftl, N2Z.inj_add; try lia.
            ** apply Z.add_lt_mono_r, (bv_unsigned_log2 (zero_lt_n)).
            ** rewrite Z.eqb_neq in x_zero. pose proof (@bv_unsigned_nonneg n x). lia.
        + destruct (bv_unsigned y =? 0)%Z eqn : y_zero;
            [ rewrite Z.eqb_eq in y_zero | rewrite Z.eqb_neq in y_zero ].
          * rewrite y_zero. cbn. lia.
          * apply (Z.lt_le_trans _ _ _ (bv_unsigned_log2 zero_lt_m)). lia.
      - apply bv_unsigned_shiftl_nonneg.
      - apply bv_unsigned_nonneg. }
Qed.

(** Give the empty bitvector an explicit name to avoid any ambiguity with the notation. *)

Definition bv_empty : bv 0 := 0.

Lemma bv_empty_bits : bv_to_bits bv_empty = [].
Proof. apply nil_length_inv. rewrite length_bv_to_bits. lia. Qed.

Lemma bv_empty_canonical : ∀ (x : bv 0), x = bv_empty.
Proof.
  intros x.
  destruct x.
  unfold bv_empty.
  bv_simplify. f_equal.
  unfold BvWf, bv_modulus  in bv_is_wf.
  rewrite Is_true_true, andb_true_iff, Z.ltb_lt, Z.leb_le in bv_is_wf.
  lia.
Qed.

(** The empty bitvector is the unit for concatentation. *)

Lemma bv_concat_unit_l : ∀ {n} {x : bv n}, bv_concat n bv_empty x = x.
Proof.
  intros n x.
  rewrite bv_concat_0; [ apply bv_zero_extend_idemp |].
  destruct x.
  unfold definitions.bv_unsigned. reflexivity.
Qed.

Lemma bv_concat_unit_r : ∀ {n} {x : bv n}, bv_concat n x bv_empty = x.
Proof.
  intros n x.
  apply bv_eq.
  rewrite bv_concat_unsigned'.
  change (bv_wrap n (Z.lor (bv_unsigned x ≪ Z.of_N 0) (bv_unsigned (bv_0 0))) = bv_unsigned x).
  rewrite (@bv_0_unsigned 0), Z.lor_0_r, Z.shiftl_0_r.
  apply bv_wrap_bv_unsigned.
Qed.

(** Now prove the full [bv_concat_app] lemma. *)

Lemma bv_concat_app : ∀ {n m} {x : bv n} {y : bv m},
  bv_to_bits (bv_concat (n + m) x y) = bv_to_bits y ++ bv_to_bits x.
Proof.
  intros n m x y.
  destruct (n =? 0)%N eqn : n_zero; [ rewrite N.eqb_eq in n_zero | rewrite N.eqb_neq in n_zero ].
  - subst.
    pose proof (bv_empty_canonical x); subst.
    rewrite bv_empty_bits, bv_concat_unit_l, app_nil_r. reflexivity.
  - destruct (m =? 0)%N eqn : m_zero; [ rewrite N.eqb_eq in m_zero | rewrite N.eqb_neq in m_zero ].
    + subst.
      pose proof (bv_empty_canonical y); subst.
      rewrite bv_empty_bits, N.add_0_r, bv_concat_unit_r. reflexivity.
    + apply bv_concat_app_non_empty; lia.
Qed.

Lemma bool_to_bv_bits : ∀ {b}, bv_to_bits (bool_to_bv 1 b) = [b].
Proof.
  intros b.
  apply (list_eq_same_length _ _ 1).
  - reflexivity.
  - rewrite length_bv_to_bits. lia.
  - intros i lb rb _ L R.
    rewrite list_lookup_singleton_Some in R. destruct R as [i_zero R].
    subst.
    rewrite bv_to_bits_lookup_Some, bool_to_bv_unsigned, bool_to_Z_spec in L; [| lia]. destruct L as [_ L].
    assert (D : bool_decide (Z.of_nat 0 = 0%Z) = true).
    { apply bool_decide_eq_true_2. lia. }
    rewrite D in L.
    naive_solver.
Qed.

Lemma bv_concat_cons : ∀ {n b} {x : bv n}, bv_to_bits (bv_concat (N.succ n) x (bool_to_bv 1 b)) = b :: bv_to_bits x.
Proof.
  intros n b x.
  pose proof (@bv_concat_app n 1 x (bool_to_bv 1 b)) as H.
  rewrite N.add_1_r, bool_to_bv_bits in H.
  exact H.
Qed.

Definition bv_cast {n m : N} (E : n = m) (x : bv n) : bv m.
Proof. rewrite E in x. exact x. Defined.

Module BoolList.
  (** Convert a list of booleans into a stdpp bitvector. The
  [bits_to_N] function does this by converting the boolean list into a
  value of type [N] by traversing the list from left to right, and
  adding a new least-significant bit to the accumulated value for each
  element of the list.

  This means it treats a list like <<[true;false;false]>> as the
  number 4, with the head element being the most significant bit.

  This seems like the most natural way to do it as it avoids any kind
  of list reversal when converting to the Rocq BinNums-based types. *)

  Definition add_lsb (b : bool) (prefix : option positive) : option positive :=
    match b with
    | false =>
        match prefix with
        | None => None
        | Some n => Some (xO n)
        end
    | true =>
        match prefix with
        | None => Some xH
        | Some n => Some (xI n)
        end
    end.

  Fixpoint bits_to_N (x : list bool) (acc : option positive) : N :=
    match x with
    | [] =>
        match acc with
        | None => N0
        | Some n => Npos n
        end
    | b :: x => bits_to_N x (add_lsb b acc)
    end.

  Definition to_Z_unsigned (x : list bool) (prefix : option positive) : Z :=
    match bits_to_N x prefix with
    | N0 => Z0
    | Npos n => Zpos n
    end.

  Fixpoint positive_to_bits (p : positive) : list bool :=
    match p with
    | xH => [true]
    | xO p => false :: positive_to_bits p
    | xI p => true :: positive_to_bits p
    end.

  Definition prefix_to_bits (prefix : option positive) : list bool :=
    match prefix with
    | None => []
    | Some p => positive_to_bits p
    end.

  Definition prefix_size (prefix : option positive) : nat :=
    match prefix with
    | None => 0
    | Some p => Pos.size_nat p
    end.

  Lemma Z_pos_size_nat : ∀ {p}, Z.of_N (N.of_nat (Pos.size_nat p)) = Z.pos (Pos.size p).
  Proof. intros p; induction p; cbn; lia. Qed.

  Lemma pow2_pos_size : ∀ {p}, (Z.pos p < 2 ^ Z.pos (Pos.size p))%Z.
  Proof.
    intros p.
    rewrite Z.log2_lt_pow2; [| lia].
    induction p; cbn; lia.
  Qed.

  Lemma to_Z_unsiged_bv_modulus : ∀ {x} prefix,
    (to_Z_unsigned x prefix < bv_modulus (N.of_nat (prefix_size prefix + length x)))%Z.
  Proof.
    intros x.
    induction x as [| [] x IH]; intros prefix.
    - destruct prefix; unfold to_Z_unsigned, bv_modulus; cbn; [| lia].
      rewrite Nat.add_0_r, Z_pos_size_nat.
      apply pow2_pos_size.
    - destruct prefix as [p |].
      + unfold to_Z_unsigned. cbn. fold (to_Z_unsigned x (Some (p~1)%positive)).
        specialize (IH (Some (p~1)%positive)).
        apply (Z.lt_le_trans _ _ _ IH).
        apply bv_modulus_le_mono.
        rewrite Nat.add_succ_r.
        reflexivity.
      + unfold to_Z_unsigned. cbn. fold (to_Z_unsigned x (Some 1%positive)).
        specialize (IH (Some 1%positive)).
        apply (Z.lt_le_trans _ _ _ IH).
        reflexivity.
    - destruct prefix as [p |].
      + unfold to_Z_unsigned. cbn. fold (to_Z_unsigned x (Some (p~0)%positive)).
        specialize (IH (Some (p~0)%positive)).
        apply (Z.lt_le_trans _ _ _ IH).
        apply bv_modulus_le_mono.
        rewrite Nat.add_succ_r.
        reflexivity.
      + unfold to_Z_unsigned. cbn. fold (to_Z_unsigned x None).
        specialize (IH None).
        apply (Z.lt_le_trans _ _ _ IH).
        apply bv_modulus_le_mono.
        cbn. lia.
  Qed.

  Definition to_bv' (x : list bool) (prefix : option positive) : bv (N.of_nat (prefix_size prefix + length x)) :=
    Z_to_bv (N.of_nat (prefix_size prefix + length x)) (to_Z_unsigned x prefix).

  (** Now, the actual function that converts a list of booleans to a stdpp bitvector. *)

  Definition to_bv (x : list bool) : bv (N.of_nat (length x)) := to_bv' x None.

  Definition positive_to_bv (p : positive) : bv (N.of_nat (Pos.size_nat p)) :=
    Z_to_bv (N.of_nat (Pos.size_nat p)) (Z.pos p).

  Lemma pos_app_1 : ∀ {p}, Z.lor (Z.pos p ≪ 1) 1 = Z.pos p~1 .
  Proof.
    intros p.
    rewrite <- shift_equiv.
    - reflexivity.
    - lia.
  Qed.

  Lemma positive_to_bv_concat_1 : ∀ {p}, positive_to_bv p~1 = bv_concat (N.of_nat (S (Pos.size_nat p))) (positive_to_bv p) (1 : bv 1).
  Proof.
    intros p.
    unfold positive_to_bv.
    bv_simplify. rewrite bv_concat_unsigned'.
    f_equal. bv_simplify. repeat rewrite bv_wrap_land.
    cbn.
    pattern (Z.land (Z.pos p) (Z.ones (Z.of_N (N.of_nat (Pos.size_nat p))))).
    rewrite Z.land_ones_low.
    - rewrite Z.land_ones_low; rewrite pos_app_1.
      + reflexivity.
      + lia.
      + destruct p; cbn; repeat (rewrite Nat2N.inj_succ + rewrite N2Z.inj_succ + rewrite Z_pos_size_nat); lia.
    - lia.
    - destruct p; cbn; try lia; rewrite Nat2N.inj_succ, N2Z.inj_succ, Z_pos_size_nat; lia.
  Qed.

  Lemma positive_to_bv_concat_0 : ∀ {p}, positive_to_bv p~0 = bv_concat (N.of_nat (S (Pos.size_nat p))) (positive_to_bv p) (0 : bv 1).
  Proof.
    intros p.
    unfold positive_to_bv.
    bv_simplify. rewrite bv_concat_unsigned'.
    f_equal. bv_simplify. repeat rewrite bv_wrap_land.
    cbn.
    pattern (Z.land (Z.pos p) (Z.ones (Z.of_N (N.of_nat (Pos.size_nat p))))).
    rewrite Z.land_ones_low.
    - rewrite Z.land_ones_low.
      + reflexivity.
      + apply Z.shiftl_nonneg; lia.
      + rewrite Z.log2_shiftl; try lia.
        destruct p; cbn; repeat (rewrite Nat2N.inj_succ + rewrite N2Z.inj_succ + rewrite Z_pos_size_nat); lia.
    - lia.
    - destruct p; cbn; try lia; rewrite Nat2N.inj_succ, N2Z.inj_succ, Z_pos_size_nat; lia.
  Qed.

  Lemma bool_to_bv_true : bool_to_bv 1 true = 1%bv.
  Proof.
    apply bv_eq.
    rewrite bool_to_bv_unsigned.
    - bv_simplify. reflexivity.
    - lia.
  Qed.

  Lemma bool_to_bv_false : bool_to_bv 1 false = 0%bv.
  Proof.
    apply bv_eq.
    rewrite bool_to_bv_unsigned.
    - bv_simplify. reflexivity.
    - lia.
  Qed.

  Lemma positive_round_trip : ∀ {p},
    bv_to_bits (positive_to_bv p) = positive_to_bits p.
  Proof with reflexivity.
    intros p.
    induction p as [p IH | p IH |]; cbn.
    - rewrite positive_to_bv_concat_1, Nat2N.inj_succ, <- bool_to_bv_true, bv_concat_cons, IH...
    - rewrite positive_to_bv_concat_0, Nat2N.inj_succ, <- bool_to_bv_false, bv_concat_cons, IH...
    - reflexivity.
  Qed.

  Lemma prefix_size_add_lsb_Some : ∀ b {p}, prefix_size (add_lsb b (Some p)) = S (prefix_size (Some p)).
  Proof. intros b prefix; destruct b; try reflexivity. Qed.

  Lemma bv_round_trip' : ∀ {x prefix}, bv_to_bits (to_bv' x prefix) = rev x ++ prefix_to_bits prefix.
  Proof.
    intros x.
    induction x as [| b x IH]; intros prefix.
    - destruct prefix as [prefix |]; try reflexivity.
      cbn. rewrite <- positive_round_trip.
      unfold to_bv', positive_to_bv. cbn. rewrite Nat.add_0_r. reflexivity.
    - destruct prefix as [p |].
      + unfold to_bv', to_Z_unsigned. cbn [bits_to_N].
        fold (to_Z_unsigned x (add_lsb b (Some p))).
        rewrite length_cons, <- Nat.add_succ_comm. rewrite <- (prefix_size_add_lsb_Some b).
        fold (to_bv' x (add_lsb b (Some p))).
        rewrite IH.
        destruct b; cbn; rewrite <- app_assoc; reflexivity.
      + destruct b.
        * unfold to_bv', to_Z_unsigned. cbn [bits_to_N add_lsb].
          fold (to_Z_unsigned x (Some 1%positive)).
          rewrite length_cons, <- Nat.add_succ_comm.
          replace (S (prefix_size None)) with (prefix_size (Some 1%positive)) by reflexivity.
          fold (to_bv' x (Some 1%positive)).
          rewrite IH.
          cbn; rewrite <- app_assoc; reflexivity.
        * specialize (IH None).
          cbn in *. rewrite app_nil_r in *.
          rewrite <- IH, <- bool_to_bv_bits, <- bv_concat_app.
          (* Implicit arguments for bv_to_bits are different *)
          rewrite N.add_1_l, <- Nat2N.inj_succ; f_equal.
          bv_simplify; f_equal.
          rewrite bv_zero_extend_unsigned; [| lia ].
          unfold to_bv'. cbn.
          repeat rewrite Z_to_bv_small; try reflexivity.
          ** split.
          *** unfold to_Z_unsigned; destruct_match; lia.
          *** apply (to_Z_unsiged_bv_modulus None).
          ** split.
          *** unfold to_Z_unsigned; destruct_match; lia.
          *** apply (Z.lt_le_trans _ _ _ (to_Z_unsiged_bv_modulus None)). reflexivity.
  Qed.

  Lemma bv_round_trip : ∀ {x}, rev (bv_to_bits (to_bv x)) = x.
  Proof.
    intros x.
    unfold to_bv.
    pose proof (@bv_round_trip' x None) as H.
    cbn in H. rewrite H, app_nil_r.
    apply rev_involutive.
  Qed.
End BoolList.
