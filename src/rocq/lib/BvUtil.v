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

Lemma bv_cast_unsigned : ∀ {n m} {x : bv n} (H : n = m), bv_unsigned (bv_cast H x) = bv_unsigned x.
Proof. intros ??? H. unfold bv_cast. rewrite <- H. reflexivity. Qed.

Lemma bv_cast_bits {n m : N} (H : n = m) (z : bv n) :
  bv_to_bits (bv_cast H z) = bv_to_bits z.
Proof. destruct H. reflexivity. Qed.

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

  Open Scope Z_scope.

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

  Definition prefix_to_Z (prefix : option positive) : Z :=
    match prefix with
    | None => Z0
    | Some p => Zpos p
    end.

  Lemma pos_shift_1 : ∀ {p}, Z.pos p ≪ 1 = Z.pos p~0.
  Proof.
    intros p.
    rewrite <- shift_equiv.
    - reflexivity.
    - lia.
  Qed.

  Lemma pos_app_1 : ∀ {p}, Z.lor (Z.pos p ≪ 1) 1 = Z.pos p~1.
  Proof.
    intros p.
    rewrite <- shift_equiv.
    - reflexivity.
    - lia.
  Qed.

  Lemma Z_shiftl_1 : ∀ {x}, x ≪ 1 = 2 * x.
  Proof. intros. rewrite Z.shiftl_mul_pow2; lia. Qed.

  Lemma Z_shiftl_S : ∀ {x n}, x ≪ Z.of_nat (S n) = (x ≪ 1) ≪ Z.of_nat n.
  Proof.
    intros x n.
    rewrite Z.shiftl_shiftl; [| lia ].
    f_equal. lia.
  Qed.

  Lemma Z_shiftl_add_distr : ∀ {a b n}, 0 ≤ n → (a ≪ n) + (b ≪ n) = (a + b) ≪ n.
  Proof.
    intros a b n H.
    repeat rewrite (Z.shiftl_mul_pow2 _ _ H).
    rewrite Z.mul_add_distr_r.
    reflexivity.
  Qed.

  Lemma Z_lor_shift_inc : ∀ {x}, (0 ≤ x)%Z → Z.lor (x ≪ 1) 1 = (x ≪ 1 + 1)%Z.
  Proof.
    intros x nonneg.
    destruct x.
    - rewrite Z_shiftl_1, Z.mul_0_r, Z.lor_0_l. lia.
    - rewrite pos_app_1, Z_shiftl_1. lia.
    - lia.
  Qed.

  Lemma Z_lor_even : ∀ {x b}, 0 ≤ x → Z.lor (2 * x) (bool_to_Z b) = 2 * x + bool_to_Z b.
  Proof.
    intros x b H.
    destruct x, b; try reflexivity.
    lia.
  Qed.

  Lemma Z_mod_even_add_1 (a n : Z) (Ha : 0 ≤ a) (Hn : n > 0) (Heven : (2 | n)%Z) :
    (2 * a) mod n + 1 = (2 * a + 1) mod n.
  Proof.
    destruct Heven as [k Hk].
    rewrite Z.mul_comm in Hk.
    subst.
    rewrite Z.add_mul_mod_distr_l, Z.mul_mod_distr_l.
    reflexivity.
    all: try lia.
  Qed.

  Lemma lsb_prefix_to_Z : ∀ {x p}, prefix_to_Z (add_lsb x p) = prefix_to_Z p ≪ 1 + bool_to_Z x.
  Proof.
    intros x p.
    destruct x, p; cbn.
    - rewrite <- shift_equiv, Pos2Z.add_pos_pos; [ reflexivity | lia ].
    - reflexivity.
    - rewrite <- pos_shift_1, Z.add_0_r. reflexivity.
    - reflexivity.
  Qed.

  Lemma to_Z_unsigned_cons : ∀ {x xs p}, to_Z_unsigned (x :: xs) p = to_Z_unsigned xs (add_lsb x p).
  Proof. intros. reflexivity. Qed.

  Lemma to_Z_unsigned_app_false : ∀ {xs p}, to_Z_unsigned (xs ++ [false]) p = to_Z_unsigned xs p ≪ 1.
  Proof.
    intros xs.
    induction xs as [| x xs IH]; intros p.
    - destruct p; cbn.
      + rewrite pos_shift_1. reflexivity.
      + rewrite Z.shiftl_0_l. reflexivity.
    - rewrite <- app_comm_cons.
      rewrite to_Z_unsigned_cons, to_Z_unsigned_cons, IH.
      reflexivity.
  Qed.

  Lemma to_Z_unsigned_app_true : ∀ {x p}, to_Z_unsigned (x ++ [true]) p = Z.lor (to_Z_unsigned x p ≪ 1) 1.
  Proof.
    intros xs.
    induction xs as [| x xs IH]; intros p.
    - destruct p; cbn.
      + rewrite pos_app_1. reflexivity.
      + rewrite Z.shiftl_0_l, Z.lor_0_l. reflexivity.
    - rewrite <- app_comm_cons.
      rewrite to_Z_unsigned_cons, to_Z_unsigned_cons, IH.
      reflexivity.
  Qed.

  Lemma to_Z_unsigned_app : ∀ {x b p}, to_Z_unsigned (x ++ [b]) p = Z.lor (to_Z_unsigned x p ≪ 1) (bool_to_Z b).
  Proof.
    intros x b p.
    destruct b.
    - rewrite to_Z_unsigned_app_true. reflexivity.
    - rewrite to_Z_unsigned_app_false. rewrite Z.lor_0_r. reflexivity.
  Qed.

  Lemma to_Z_unsigned_nil : ∀ {p}, to_Z_unsigned [] p = prefix_to_Z p.
  Proof. intros. destruct p as [? |]; reflexivity. Qed.

  Lemma to_Z_unsigned_split : ∀ {x p}, to_Z_unsigned x p = prefix_to_Z p ≪ Z.of_nat (length x) + to_Z_unsigned x None.
  Proof.
    intros xs.
    induction xs as [| x xs IH]; intros p; cbn.
    - rewrite to_Z_unsigned_nil, Z.shiftl_0_r, Z.add_0_r.
      reflexivity.
    - rewrite to_Z_unsigned_cons, to_Z_unsigned_cons, (IH (add_lsb x p)), (IH (add_lsb x None)).
      rewrite lsb_prefix_to_Z, lsb_prefix_to_Z.
      cbn. rewrite Z.shiftl_0_l, Z.add_0_l, Z_shiftl_1, Z_shiftl_S, Z_shiftl_1, Z.add_assoc, Z_shiftl_add_distr.
      + reflexivity.
      + lia.
  Qed.

  Lemma to_Z_unsigned_nonneg : ∀ x p, 0 ≤ to_Z_unsigned x p.
  Proof. intros. unfold to_Z_unsigned. destruct_match; lia. Qed.

  Lemma Z_pos_size_nat : ∀ {p}, Z.of_N (N.of_nat (Pos.size_nat p)) = Z.pos (Pos.size p).
  Proof. intros p; induction p; cbn; lia. Qed.

  Lemma pow2_pos_size : ∀ {p}, Z.pos p < 2 ^ Z.pos (Pos.size p).
  Proof.
    intros p.
    rewrite Z.log2_lt_pow2; [| lia].
    induction p; cbn; lia.
  Qed.

  Lemma to_Z_unsiged_bv_modulus : ∀ {x} prefix,
    to_Z_unsigned x prefix < bv_modulus (N.of_nat (prefix_size prefix + length x)).
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

  Lemma to_bv_unsigned : ∀ {xs}, bv_unsigned (to_bv xs) = to_Z_unsigned xs None.
  Proof.
    intros xs.
    unfold to_bv, to_bv'.
    rewrite Z_to_bv_small; [ reflexivity |].
    split.
    - unfold to_Z_unsigned. destruct_match; lia.
    - apply (to_Z_unsiged_bv_modulus None).
  Qed.

  Definition positive_to_bv (p : positive) : bv (N.of_nat (Pos.size_nat p)) :=
    Z_to_bv (N.of_nat (Pos.size_nat p)) (Z.pos p).

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

  Lemma bv_round_trip_alt : ∀ {x}, bv_to_bits (to_bv x) = rev x.
  Proof.
    intros x.
    unfold to_bv.
    pose proof (@bv_round_trip' x None) as H.
    cbn in H. rewrite H, app_nil_r.
    reflexivity.
  Qed.

  Lemma bv_round_trip : ∀ {x}, rev (bv_to_bits (to_bv x)) = x.
  Proof. intros. rewrite bv_round_trip_alt. apply rev_involutive. Qed.

  Lemma to_bv_ex : ∀ {n} (x : bv n), ∃ y, N.of_nat (length y) = n ∧ ∀ (H : N.of_nat (length y) = n), x = bv_cast H (to_bv y).
  Proof.
    intros n x.
    exists (rev (bv_to_bits x)).
    split.
    - simp_length.
    - intros H.
      symmetry.
      apply (inj bv_to_bits).
      rewrite bv_cast_bits.
      unfold to_bv.
      pose proof (@bv_round_trip' (rev (bv_to_bits x)) None) as Hrt.
      cbn in Hrt. rewrite app_nil_r, rev_involutive in Hrt.
      exact Hrt.
  Qed.

  Fixpoint carry_in_rev (c : bool) (xs : list bool) : list bool :=
    if c then
      match xs with
      | [] => [c]
      | false :: xs => true :: xs
      | true :: xs => false :: carry_in_rev true xs
      end
    else xs.

  Definition carry_in (c : bool) (xs : list bool) : list bool := rev (carry_in_rev c (rev xs)).

  Lemma carry_in_false : ∀ {xs}, carry_in false xs = xs.
  Proof.
    intros xs.
    destruct xs as [| x xs _] using rev_ind.
    - reflexivity.
    - unfold carry_in. rewrite rev_unit. cbn. rewrite rev_involutive. reflexivity.
  Qed.

  Lemma carry_in_to_Z : ∀ {c xs}, to_Z_unsigned (carry_in c xs) None = (to_Z_unsigned xs None + bool_to_Z c)%Z.
  Proof.
    intros c xs.
    revert c.
    induction xs as [| x xs IH] using rev_ind; intros c.
    - cbn. destruct_match; cbn; lia.
    - unfold carry_in. rewrite rev_unit.
      destruct c, x; cbn; [ fold (carry_in true xs) | | |]; cbn.
      all: repeat first [ rewrite rev_involutive | rewrite to_Z_unsigned_app_true | rewrite to_Z_unsigned_app_false ].
      all: try rewrite IH.
      all: try (repeat rewrite Z_shiftl_1; cbn; lia).
      all: cbn.
      + rewrite Z_lor_shift_inc, Z_shiftl_1, Z_shiftl_1; [ lia | apply to_Z_unsigned_nonneg ].
      + rewrite Z_lor_shift_inc; [ reflexivity | apply to_Z_unsigned_nonneg ].
  Qed.

  Lemma carry_in_app_true : ∀ {c xs}, carry_in c (xs ++ [true]) = carry_in c xs ++ [xorb c true].
  Proof.
    intros c xs.
    unfold carry_in. rewrite rev_unit.
    destruct c; cbn [carry_in_rev xorb rev].
    - reflexivity.
    - fold (carry_in false xs). rewrite carry_in_false, rev_involutive. reflexivity.
  Qed.

  Lemma carry_in_app : ∀ {c x xs}, carry_in c (xs ++ [x]) = carry_in (andb c x) xs ++ [xorb c x].
  Proof.
    intros c x xs.
    destruct x.
    - rewrite andb_true_r. apply carry_in_app_true.
    - rewrite andb_false_r, carry_in_false.
      unfold carry_in. rewrite rev_unit.
      destruct c; cbn [carry_in_rev xorb rev]; rewrite rev_involutive; reflexivity.
  Qed.

  Lemma to_Z_unsigned_testbit : ∀ {xs i b}, (rev xs) !! i = Some b → Z.testbit (to_Z_unsigned xs None) (Z.of_nat i) = b.
  Proof.
    intros xs.
    induction xs as [| x xs IH] using rev_ind; intros i b H.
    - cbn in H. rewrite lookup_nil in H. discriminate.
    - rewrite to_Z_unsigned_app, Z.lor_spec, Z.shiftl_spec; [| lia].
      destruct i.
      + rewrite Z.testbit_neg_r, orb_false_l; [| lia].
        rewrite rev_unit in H. cbn in H. inversion H; subst.
        rewrite bool_to_Z_spec.
        assert (D : bool_decide (Z.of_nat 0 = 0%Z) = true).
        { apply bool_decide_eq_true_2. lia. }
        rewrite D, andb_true_l.
        reflexivity.
      + rewrite bool_to_Z_spec.
        assert (D: bool_decide (Z.of_nat (S i) = 0%Z) = false).
        { apply bool_decide_eq_false_2. lia. }
        rewrite D, andb_false_l, orb_false_r.
        replace (Z.of_nat (S i) - 1)%Z with (Z.of_nat i); [| lia].
        rewrite (IH _ b); [ reflexivity |].
        rewrite <- H, rev_unit, <- lookup_tail.
        reflexivity.
  Qed.

  Definition bool_add_carry (x y c : bool) : bool * bool :=
    match (x, y, c) with
    | (false, false, false) => (false, false)
    | (false, false, true ) => (true,  false)
    | (false, true,  false) => (true,  false)
    | (false, true,  true ) => (false, true)
    | (true,  false, false) => (true,  false)
    | (true,  false, true ) => (false, true)
    | (true,  true,  false) => (false, true)
    | (true,  true,  true ) => (true,  true)
    end.

  Lemma add_carry_step : ∀ {zs} {x y} {xp yp} {z} {in_c out_c},
    bool_add_carry x y in_c = (z, out_c) →
    to_Z_unsigned zs None = (prefix_to_Z xp + prefix_to_Z yp)%Z →
    to_Z_unsigned (carry_in out_c zs ++ [z]) None = (prefix_to_Z (add_lsb x xp) + prefix_to_Z (add_lsb y yp) + bool_to_Z in_c)%Z.
  Proof.
    intros zs x y xp yp z c c' Add Tail.
    destruct z.
    - rewrite to_Z_unsigned_app_true, carry_in_to_Z, Tail.
      destruct x, y, c, c', xp, yp; cbn in *; try discriminate.
      all: try (rewrite Z_lor_shift_inc; [| lia]).
      all: try rewrite Z_shiftl_1.
      all: lia.
    - rewrite to_Z_unsigned_app_false, BoolList.carry_in_to_Z, Tail.
      destruct x, y, c, c', xp, yp; cbn in *; try discriminate.
      all: try rewrite BoolList.Z_shiftl_1.
      all: lia.
  Qed.

  Fixpoint add_carry_acc (xs ys : list bool) (c : bool) (zs : list bool) : list bool * bool :=
    match xs with
    | [] => (zs, c)
    | x :: xs =>
        match ys with
        | [] =>
            let '(z, c) := bool_add_carry x false c in
            add_carry_acc xs ys c (z :: zs)
        | y :: ys =>
            let '(z, c) := bool_add_carry x y c in
            add_carry_acc xs ys c (z :: zs)
        end
    end.

  Definition add_carry (xs ys : list bool) : list bool * bool :=
    add_carry_acc (rev xs) (rev ys) false [].

  Lemma add_carry_acc_to_Z : ∀ xs ys c zs,
    length xs = length ys →
    to_Z_unsigned (add_carry_acc (rev xs) (rev ys) c zs).1 None =
      ((to_Z_unsigned xs None + to_Z_unsigned ys None + bool_to_Z c) `mod` 2 ^ Z.of_nat (length xs))
      ≪ Z.of_nat (length zs) + to_Z_unsigned zs None.
  Proof.
    intros xs.
    induction xs as [| x xs IH] using rev_ind; intros ys c zs L.
    - assert (ys_nil : ys = []).
      { apply nil_length_inv. naive_solver. }
      subst. cbn.
      rewrite Z.mod_1_r, Z.shiftl_0_l.
      reflexivity.
    - rewrite length_app in L. cbn in L. rewrite Nat.add_1_r in L.
      destruct ys as [| y ys _] using rev_ind; [ discriminate |].
      rewrite length_app in L; cbn in L. rewrite Nat.add_1_r in L. apply eq_add_S in L.
      unfold add_carry.
      repeat rewrite rev_unit.
      cbn [add_carry_acc].
      destruct (bool_add_carry x y c) as (z, c') eqn : Add.
      specialize (IH ys c' (z :: zs) L).
      rewrite IH.
      repeat rewrite to_Z_unsigned_app.
      repeat rewrite Z_shiftl_1, Z_lor_even; try apply to_Z_unsigned_nonneg.
      cbn [length].
      rewrite Z_shiftl_S, Z_shiftl_1.
      rewrite to_Z_unsigned_cons.
      repeat rewrite Z.add_assoc.
      rewrite <- Zmult_mod_distr_l.
      replace (2 ^ Z.of_nat (length (xs ++ [x])))%Z
        with (2 * 2 ^ Z.of_nat (length xs))%Z; [| shelve ].
      assert (Lxyc : (bool_to_Z x + bool_to_Z y + bool_to_Z c = bool_to_Z z + 2 * bool_to_Z c')%Z).
      { destruct x, y, z, c, c'; cbn in Add |- *; discriminate + reflexivity. }
      repeat rewrite Z.mul_add_distr_l.
      replace (2 * to_Z_unsigned xs None + bool_to_Z x + 2 * to_Z_unsigned ys None + bool_to_Z y + bool_to_Z c)%Z
        with (2 * to_Z_unsigned xs None + 2 * to_Z_unsigned ys None + (bool_to_Z x + bool_to_Z y + bool_to_Z c))%Z; [| lia].
      rewrite Lxyc.
      repeat rewrite Z.add_assoc.
      rewrite (@to_Z_unsigned_split zs (add_lsb z None)).
      rewrite Z.add_assoc, Z_shiftl_add_distr, lsb_prefix_to_Z; [| lia].
      repeat f_equal.
      destruct z.
      + cbn.
        replace (2 * to_Z_unsigned xs None + 2 * to_Z_unsigned ys None + 1 + 2 * bool_to_Z c')%Z
          with (2 * (to_Z_unsigned xs None + to_Z_unsigned ys None + bool_to_Z c') + 1)%Z; [| lia].
        rewrite <- Z_mod_even_add_1; [ repeat f_equal; lia | shelve | lia | apply Z.divide_factor_l ].
      + cbn. rewrite Z.add_0_r, Z.add_0_r. reflexivity.
      Unshelve.
      { rewrite length_app. cbn. rewrite Nat.add_1_r, Nat2Z.inj_succ, Z.pow_succ_r.
        - reflexivity.
        - lia. }
      { apply Z.add_nonneg_nonneg;
          [ apply Z.add_nonneg_nonneg; apply to_Z_unsigned_nonneg | destruct c'; cbn; lia ]. }
  Qed.

  Lemma add_carry_to_Z (xs ys : list bool) :
    length xs = length ys →
    to_Z_unsigned (add_carry xs ys).1 None =
      (to_Z_unsigned xs None + to_Z_unsigned ys None) `mod` 2 ^ Z.of_nat (length xs).
  Proof.
    intros H.
    unfold add_carry.
    rewrite (add_carry_acc_to_Z _ _ _ _ H).
    cbn. rewrite Z.shiftl_0_r, Z.add_0_r, Z.add_0_r.
    reflexivity.
  Qed.
End BoolList.
