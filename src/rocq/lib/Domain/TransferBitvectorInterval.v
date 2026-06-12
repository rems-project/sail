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

From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import ZArith.

From stdpp Require Import base.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import bitvector.tactics.

From Sail Require Import Domain.Lattice.
From Sail.Domain Require AbsBitvector.
From Sail.Domain Require Interval.
From Sail Require Bit.
From Sail Require Import BvUtil.

Import Bit.Three.

Module B := AbsBitvector.Dom.
Module I := Interval.Dom.

Module BP := DomainProperties Lattice.Bits B.

Module Ops <: SAIL_BITS_INT B I.

  Definition nonneg_top : I.t :=
    I.Ends (exist _ (Some 0%Z, None) (I.low_high_plus_inf 0%Z)).

  (* Minimum unsigned value of abstract bits (LSB-first), `pow` is the weight of the first bit *)
  Fixpoint unsigned_lo (bits : list ubit) (pow : Z) : Z :=
    match bits with
    | []         => 0%Z
    | B0 :: rest => unsigned_lo rest (2 * pow)%Z
    | B1 :: rest => (pow + unsigned_lo rest (2 * pow))%Z
    | BU :: rest => unsigned_lo rest (2 * pow)%Z
    end.

  (* Maximum unsigned value of abstract bits (LSB-first) *)
  Fixpoint unsigned_hi (bits : list ubit) (pow : Z) : Z :=
    match bits with
    | []         => 0%Z
    | B0 :: rest => unsigned_hi rest (2 * pow)%Z
    | B1 :: rest => (pow + unsigned_hi rest (2 * pow))%Z
    | BU :: rest => (pow + unsigned_hi rest (2 * pow))%Z
    end.

  Definition bits_unsigned_interval (bits : list ubit) : I.t :=
    I.join (I.α (unsigned_lo bits 1%Z)) (I.α (unsigned_hi bits 1%Z)).

  (* For each width in the abstract bitvector map, compute and join unsigned intervals *)
  Definition unsigned (x : B.t) : I.t :=
    match x with
    | B.Top   => nonneg_top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          I.join (bits_unsigned_interval bits) acc) I.bot (`m)
    end.

  Lemma I_join_idem : ∀ x : I.t, I.join x x = x.
  Proof.
    intros x.
    rewrite <- (I.meet_id x) at 2.
    apply I.absorption_join_meet.
  Qed.

  Lemma concrete_lo_eq_hi : ∀ (bs : list bool) (pow : Z),
    unsigned_lo (List.map from_bool bs) pow = unsigned_hi (List.map from_bool bs) pow.
  Proof.
    intros bs.
    induction bs as [| b bs IH]; intros pow.
    - reflexivity.
    - destruct b; cbn; rewrite IH; reflexivity.
  Qed.

  Lemma unsigned_lo_spec : ∀ (bs : list bool) (pow : Z),
    (0 ≤ pow)%Z →
    (unsigned_lo (List.map from_bool bs) pow =
     pow * BoolList.to_Z_unsigned (rev bs) None)%Z.
  Proof.
    induction bs as [| b bs IH]; intros pow Hpow.
    - cbn. lia.
    - cbn [List.map rev List.app].
      rewrite BoolList.to_Z_unsigned_app, BoolList.Z_shiftl_1, BoolList.Z_lor_even;
        [| apply BoolList.to_Z_unsigned_nonneg].
      specialize (IH (2 * pow)%Z ltac:(lia)).
      destruct b; cbn; rewrite IH; lia.
  Qed.

  Lemma bv_unsigned_to_Z : ∀ {n} (x : bv n),
    bv_unsigned x = BoolList.to_Z_unsigned (rev (bv_to_bits x)) None.
  Proof.
    intros n x.
    pose proof (BoolList.to_bv_ex x) as [y [Hlen Heq]].
    specialize (Heq Hlen).
    assert (Hbits : bv_to_bits x = rev y).
    { rewrite Heq, bv_cast_bits. apply BoolList.bv_round_trip_alt. }
    rewrite Hbits, rev_involutive.
    rewrite Heq, bv_cast_unsigned.
    apply BoolList.to_bv_unsigned.
  Qed.

  Lemma unsigned_abst : ∀ {n} {x : bv n},
    I.α (bv_unsigned x) = unsigned (B.α (bv_to_bvn x)).
  Proof.
    intros n x.
    rewrite B.abstract_bvs.
    unfold unsigned, bits_unsigned_interval.
    cbn [proj1_sig].
    rewrite map_fold_singleton, I.join_id.
    rewrite <- concrete_lo_eq_hi, I_join_idem.
    f_equal.
    rewrite unsigned_lo_spec; [| lia].
    rewrite Z.mul_1_l.
    exact (bv_unsigned_to_Z x).
  Qed.

  (* Signed interval from abstract bits: sign bit (MSB) contributes -2^(n-1) instead of +2^(n-1) *)
  Definition bits_signed_interval (bits : list ubit) : I.t :=
    match rev bits with
    | [] => I.α 0%Z
    | sign :: lower_rev =>
        let lower := rev lower_rev in
        let lo    := unsigned_lo lower 1%Z in
        let hi    := unsigned_hi lower 1%Z in
        let half  := (2 ^ Z.of_nat (length lower))%Z in
        match sign with
        | B0 => I.join (I.α lo) (I.α hi)
        | B1 => I.join (I.α (lo - half)%Z) (I.α (hi - half)%Z)
        | BU => I.join (I.α (lo - half)%Z) (I.α hi)
        end
    end.

  Definition signed (x : B.t) : I.t :=
    match x with
    | B.Top   => I.top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          I.join (bits_signed_interval bits) acc) I.bot (`m)
    end.

  Lemma to_Z_unsigned_cons_None : ∀ (b : bool) (bs : list bool),
    (BoolList.to_Z_unsigned (b :: bs) None =
     bool_to_Z b * 2 ^ Z.of_nat (length bs) + BoolList.to_Z_unsigned bs None)%Z.
  Proof.
    intros b bs.
    rewrite BoolList.to_Z_unsigned_cons, BoolList.to_Z_unsigned_split.
    rewrite BoolList.lsb_prefix_to_Z.
    cbn [BoolList.prefix_to_Z].
    rewrite Z.shiftl_0_l, Z.add_0_l.
    rewrite Z.shiftl_mul_pow2; [reflexivity | lia].
  Qed.

  Lemma unsigned_lo_concrete_rev : ∀ (bs : list bool),
    (unsigned_lo (List.map from_bool (rev bs)) 1%Z = BoolList.to_Z_unsigned bs None)%Z.
  Proof.
    intros bs.
    rewrite unsigned_lo_spec; [| lia].
    rewrite Z.mul_1_l, rev_involutive.
    reflexivity.
  Qed.

  Lemma bv_swrap_sign : ∀ (n : N) (s : bool) (lo : Z),
    n ≠ 0%N →
    (0 ≤ lo)%Z → (lo < bv_half_modulus n)%Z →
    bv_swrap n (bool_to_Z s * bv_half_modulus n + lo)%Z =
    (lo - bool_to_Z s * bv_half_modulus n)%Z.
  Proof.
    intros n s lo Hn Hlo_nn Hlo_lt.
    pose proof (bv_half_modulus_twice n Hn) as Htwice.
    pose proof (bv_half_modulus_nonneg n) as Hhalf_nn.
    pose proof (bv_modulus_pos n) as Hmod_pos.
    unfold bv_swrap, bv_wrap.
    destruct s; cbn [bool_to_Z].
    - replace (1 * bv_half_modulus n + lo + bv_half_modulus n)%Z
        with (lo + 1 * bv_modulus n)%Z by lia.
      rewrite Z.mod_add; [| lia].
      rewrite Z.mod_small; lia.
    - replace (0 * bv_half_modulus n + lo + bv_half_modulus n)%Z
        with (lo + bv_half_modulus n)%Z by lia.
      rewrite Z.mod_small; lia.
  Qed.

  Lemma signed_abst : ∀ {n} {x : bv n},
    I.α (bv_signed x) = signed (B.α (bv_to_bvn x)).
  Proof.
    intros n x.
    rewrite B.abstract_bvs.
    unfold signed.
    cbn [proj1_sig].
    rewrite map_fold_singleton, I.join_id.
    destruct (decide (n = 0%N)) as [-> | Hn].
    - rewrite (bv_empty_canonical x), bv_empty_bits.
      cbn. rewrite bv_signed_N_0. reflexivity.
    - unfold bits_signed_interval.
      rewrite <- map_rev.
      assert (Hlen : length (rev (bv_to_bits x)) = N.to_nat n).
      { rewrite length_rev. apply length_bv_to_bits. }
      destruct (rev (bv_to_bits x)) as [| sign rest] eqn : Hrev.
      + exfalso.
        cbn in Hlen.
        destruct n; [exact (Hn eq_refl) | lia].
      + set (k := length rest).
        assert (Hk : S k = N.to_nat n).
        { cbn in Hlen. unfold k. exact Hlen. }
        assert (Hn_eq : n = N.of_nat (S k)).
        { symmetry. rewrite Hk. apply N2Nat.id. }
        set (lo := BoolList.to_Z_unsigned rest None).
        assert (Hunsigned : bv_unsigned x = (bool_to_Z sign * 2 ^ Z.of_nat k + lo)%Z).
        { unfold lo.
          rewrite bv_unsigned_to_Z, Hrev.
          apply to_Z_unsigned_cons_None. }
        assert (Hlo_nn : (0 ≤ lo)%Z) by apply BoolList.to_Z_unsigned_nonneg.
        assert (Hhalf_eq : bv_half_modulus n = (2 ^ Z.of_nat k)%Z).
        { pose proof (bv_half_modulus_twice n Hn) as Htwice.
          unfold bv_modulus in Htwice.
          rewrite Hn_eq, nat_N_Z, Nat2Z.inj_succ, Z.pow_succ_r in Htwice; [| lia].
          rewrite Hn_eq. lia. }
        assert (Hlo_lt : (lo < bv_half_modulus n)%Z).
        { rewrite Hhalf_eq.
          unfold lo.
          pose proof (@BoolList.to_Z_unsiged_bv_modulus rest None) as H.
          cbn [BoolList.prefix_size] in H. rewrite Nat.add_0_l in H.
          unfold bv_modulus in H. rewrite nat_N_Z in H.
          exact H. }
        assert (Hsigned : bv_signed x = (lo - bool_to_Z sign * 2 ^ Z.of_nat k)%Z).
        { unfold bv_signed.
          rewrite Hunsigned, <- Hhalf_eq.
          apply bv_swrap_sign; [exact Hn | exact Hlo_nn | exact Hlo_lt]. }
        cbn [List.map].
        rewrite <- map_rev.
        assert (Hlo_eq : unsigned_lo (List.map from_bool (rev rest)) 1%Z = lo).
        { unfold lo. apply unsigned_lo_concrete_rev. }
        assert (Hhi_eq : unsigned_hi (List.map from_bool (rev rest)) 1%Z = lo).
        { rewrite <- (concrete_lo_eq_hi (rev rest) 1). exact Hlo_eq. }
        rewrite Hlo_eq, Hhi_eq.
        assert (Hlen_k : length (List.map from_bool (rev rest)) = k).
        { rewrite length_map, length_rev. reflexivity. }
        rewrite Hlen_k, Hsigned.
        destruct sign; cbn [from_bool bool_to_Z]; rewrite I_join_idem; f_equal; lia.
  Qed.

  Definition zeros_nat (n : nat) : B.t := B.α (bv_0 (N.of_nat n)).

  Definition ones_nat (n : nat) : B.t := B.α (bv_not (bv_0 (N.of_nat n))).

  (** This function intersects an interval with <<[0,∞)>>, converting
      the resulting endpoints to natural numbers. Returns [None] if
      the resulting interval is empty. For the upper bound, [None]
      represents <<∞>>. *)
  Definition nonneg_range (n : I.t) : option (nat * option nat) :=
    match n with
    | I.Empty => None
    | I.Ends endpoints =>
       match proj1_sig endpoints with
       | (None, None) => Some (0, None)
       | (Some lo, None) => Some (Z.to_nat lo, None)
       | (None, Some hi) =>
           if (hi <? 0)%Z then None else Some (0, Some (Z.to_nat hi))
       | (Some lo, Some hi) =>
           if (hi <? 0)%Z then None else Some (Z.to_nat lo, Some (Z.to_nat hi))
       end
    end.

  Definition zeros (h : nat) (n : I.t) : B.t :=
    match nonneg_range n with
    | None => B.bot
    | Some (_, None) => B.top
    | Some (lo, Some hi) =>
        let widths := hi - lo in
        if h <=? widths then
          B.top
        else
          fold_left (fun b w => B.join b (zeros_nat w)) (seq lo (hi - lo)) (zeros_nat hi)
    end.

  Lemma N_to_nat_via_Z : ∀ n, Z.to_nat (Z.of_N n) = N.to_nat n.
  Proof.
    destruct n.
    - cbn. rewrite Z2Nat.inj_0, N2Nat.inj_0. reflexivity.
    - rewrite N2Z.inj_pos, positive_N_nat, Z2Nat.inj_pos. reflexivity.
  Qed.

  Lemma zeros_abst : ∀ {n : N} h,
    B.le (B.α (bv_0 n)) (zeros h (I.α (Z.of_N n))).
  Proof.
    intros n h.
    unfold I.α, zeros. cbn.
    assert (Positive : (Z.of_N n <? 0)%Z = false).
    { destruct n; reflexivity. }
    rewrite Positive, Nat.sub_diag.
    destruct h; cbn.
    - apply BP.le_top.
    - unfold zeros_nat. rewrite N_to_nat_via_Z, N2Nat.id.
      apply BP.le_refl.
  Qed.

  Definition ones (h : nat) (n : I.t) : B.t :=
    match nonneg_range n with
    | None => B.bot
    | Some (_, None) => B.top
    | Some (lo, Some hi) =>
        let widths := hi - lo in
        if h <=? widths then
          B.top
        else
          fold_left (fun b w => B.join b (ones_nat w)) (seq lo (hi - lo)) (ones_nat hi)
    end.

  Lemma ones_abst : ∀ {n} h,
    B.le (B.α (bv_not (bv_0 n))) (ones h (I.α (Z.of_N n))).
  Proof.
    intros n h.
    unfold I.α, ones. cbn.
    assert (Positive : (Z.of_N n <? 0)%Z = false).
    { destruct n; reflexivity. }
    rewrite Positive, Nat.sub_diag.
    destruct h; cbn.
    - apply BP.le_top.
    - unfold ones_nat. rewrite N_to_nat_via_Z, N2Nat.id.
      apply BP.le_refl.
  Qed.

  (** Number of consecutive B0 bits from the front of the list (min
      CLZ/CTZ: first non-B0 might be 1) *)
  Fixpoint count_leading_B0 (bits : list ubit) : nat :=
    match bits with
    | B0 :: rest => 1 + count_leading_B0 rest
    | _          => 0
    end.

  (** Number of bits until the first definite B1 (max CLZ/CTZ: BU bits
      might all be 0) *)
  Fixpoint count_until_B1 (bits : list ubit) : nat :=
    match bits with
    | []        => 0
    | B1 :: _   => 0
    | _ :: rest => 1 + count_until_B1 rest
    end.

  Definition bits_clz_interval (bits : list ubit) : I.t :=
    let rev_bits := rev bits in
    let lo := Z.of_nat (count_leading_B0 rev_bits) in
    let hi := Z.of_nat (count_until_B1 rev_bits) in
    I.join (I.α lo) (I.α hi).

  Definition count_leading_zeros (x : B.t) : I.t :=
    match x with
    | B.Top   => nonneg_top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          I.join (bits_clz_interval bits) acc) I.bot (`m)
    end.

  Definition bits_ctz_interval (bits : list ubit) : I.t :=
    let lo := Z.of_nat (count_leading_B0 bits) in
    let hi := Z.of_nat (count_until_B1 bits) in
    I.join (I.α lo) (I.α hi).

  Definition count_trailing_zeros (x : B.t) : I.t :=
    match x with
    | B.Top   => nonneg_top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          I.join (bits_ctz_interval bits) acc) I.bot (`m)
    end.

  Lemma zero_extend_one_width_valid (src_bits : list ubit) (dst_w : nat) :
    length src_bits ≤ dst_w →
    B.valid {[dst_w := src_bits ++ replicate (dst_w - length src_bits) B0]}.
  Proof.
    intros H. apply B.singleton_valid.
    rewrite length_app, length_replicate. lia.
  Qed.

  (** Extend a single abstract bits list to dst_w by appending B0 padding. *)
  Definition zero_extend_one_width (src_bits : list ubit) (dst_w : nat) : B.t :=
    let src_w := length src_bits in
    match decide (src_w ≤ dst_w) with
    | left Hle =>
        B.Bvs ({[dst_w := src_bits ++ replicate (dst_w - src_w) B0]} ↾
               zero_extend_one_width_valid src_bits dst_w Hle)
    | right _ => B.bot
    end.

  (** Join zero-extensions of all width entries in b to a single target width. *)
  Definition zero_extend_to_width (b : B.t) (dst_w : nat) : B.t :=
    match b with
    | B.Top => B.top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          B.join (zero_extend_one_width bits dst_w) acc) B.bot (`m)
    end.

  Definition zero_extend (h : nat) (b : B.t) (n : I.t) : B.t :=
    match nonneg_range n with
    | None => B.bot
    | Some (_, None) => B.top
    | Some (lo, Some hi) =>
        let widths := hi - lo in
        if h <=? widths then
          B.top
        else
          fold_left (fun acc w => B.join acc (zero_extend_to_width b w))
                    (seq lo (hi - lo)) (zero_extend_to_width b hi)
    end.

  Lemma sign_extend_one_width_valid (src_bits : list ubit) (sign : ubit) (dst_w : nat) :
    length src_bits ≤ dst_w →
    B.valid {[dst_w := src_bits ++ replicate (dst_w - length src_bits) sign]}.
  Proof.
    intros H. apply B.singleton_valid.
    rewrite length_app, length_replicate. lia.
  Qed.

  (** Extend a single abstract bits list to dst_w by replicating the MSB (sign bit). *)
  Definition sign_extend_one_width (src_bits : list ubit) (dst_w : nat) : B.t :=
    let src_w := length src_bits in
    match decide (src_w ≤ dst_w) with
    | left Hle =>
        let sign := match rev src_bits with
                    | s :: _ => s
                    | []     => B0
                    end in
        B.Bvs ({[dst_w := src_bits ++ replicate (dst_w - src_w) sign]} ↾
               sign_extend_one_width_valid src_bits sign dst_w Hle)
    | right _ => B.bot
    end.

  (** Join sign-extensions of all width entries in b to a single target width. *)
  Definition sign_extend_to_width (b : B.t) (dst_w : nat) : B.t :=
    match b with
    | B.Top => B.top
    | B.Bvs m =>
        map_fold (λ (_ : nat) bits acc,
          B.join (sign_extend_one_width bits dst_w) acc) B.bot (`m)
    end.

  Definition sign_extend (h : nat) (b : B.t) (n : I.t) : B.t :=
    match nonneg_range n with
    | None => B.bot
    | Some (_, None) => B.top
    | Some (lo, Some hi) =>
        let widths := hi - lo in
        if h <=? widths then
          B.top
        else
          fold_left (fun acc w => B.join acc (sign_extend_to_width b w))
                    (seq lo (hi - lo)) (sign_extend_to_width b hi)
    end.

  Lemma bv_zero_extend_bits : ∀ {n : N} (z : N) (x : bv n),
    (n ≤ z)%N →
    bv_to_bits (bv_zero_extend z x) = bv_to_bits x ++ replicate (N.to_nat z - N.to_nat n) false.
  Proof.
    intros n z x Hnz.
    assert (Hn_le : N.to_nat n ≤ N.to_nat z).
    { apply N2Z.inj_le in Hnz. rewrite <- (N2Nat.id n), <- (N2Nat.id z), !nat_N_Z in Hnz. lia. }
    apply (list_eq_same_length _ _ (N.to_nat z)).
    - rewrite length_app, length_bv_to_bits, length_replicate. lia.
    - rewrite length_bv_to_bits. reflexivity.
    - intros i b1 b2 Hi L R.
      rewrite bv_to_bits_lookup_Some in L. destruct L as [_ ->].
      rewrite bv_zero_extend_unsigned; [| exact Hnz].
      destruct (Nat.lt_ge_cases i (N.to_nat n)) as [Hi_lo | Hi_hi].
      + rewrite lookup_app_l in R; [| rewrite length_bv_to_bits; exact Hi_lo].
        rewrite bv_to_bits_lookup_Some in R. destruct R as [_ ->].
        reflexivity.
      + rewrite lookup_app_r in R; [| rewrite length_bv_to_bits; exact Hi_hi].
        rewrite length_bv_to_bits in R.
        apply lookup_replicate_1 in R. destruct R as [-> _].
        apply bv_unsigned_spec_high.
        rewrite <- (N2Nat.id n), nat_N_Z. lia.
  Qed.

  Lemma zero_extend_abst : ∀ {n : N} {x : bv n} {z : N} h,
    (n ≤ z)%N →
    B.le (B.α (bv_zero_extend z x)) (zero_extend h (B.α (bv_to_bvn x)) (I.α (Z.of_N z))).
  Proof.
    intros n x z h Hnz.
    assert (Hn_le : N.to_nat n ≤ N.to_nat z).
    { apply N2Z.inj_le in Hnz. rewrite <- (N2Nat.id n), <- (N2Nat.id z), !nat_N_Z in Hnz. lia. }
    unfold I.α, zero_extend. cbn.
    assert (Positive : (Z.of_N z <? 0)%Z = false) by (destruct z; reflexivity).
    rewrite Positive, Nat.sub_diag.
    destruct h; cbn.
    - apply BP.le_top.
    - rewrite N_to_nat_via_Z.
      unfold zero_extend_to_width.
      rewrite (B.abstract_bvs x). cbn [proj1_sig].
      rewrite map_fold_singleton, B.join_id.
      unfold zero_extend_one_width.
      destruct (decide (length (map from_bool (bv_to_bits x)) ≤ N.to_nat z)) as [Hd | Hd].
      + assert (Heq : B.α (bv_zero_extend z x) =
                      B.Bvs ({[N.to_nat z := map from_bool (bv_to_bits x) ++
                               replicate (N.to_nat z - length (map from_bool (bv_to_bits x))) B0]}
                             ↾ zero_extend_one_width_valid _ _ Hd)).
        { rewrite B.abstract_bvs. f_equal. apply subset_eq_compat.
          rewrite bv_zero_extend_bits; [| exact Hnz].
          rewrite map_app, fmap_replicate.
          rewrite length_map, length_bv_to_bits. reflexivity. }
        rewrite Heq. apply BP.le_refl.
      + exfalso. apply Hd. rewrite (length_map from_bool), length_bv_to_bits. exact Hn_le.
  Qed.

  Lemma bv_sign_extend_bits : ∀ {n : N} (z : N) (x : bv n),
    (n ≤ z)%N →
    bv_to_bits (bv_sign_extend z x) =
    bv_to_bits x ++ replicate (N.to_nat z - N.to_nat n) (hd false (rev (bv_to_bits x))).
  Proof.
    intros n z x Hnz.
    assert (Hn_le : N.to_nat n ≤ N.to_nat z).
    { apply N2Z.inj_le in Hnz. rewrite <- (N2Nat.id n), <- (N2Nat.id z), !nat_N_Z in Hnz. lia. }
    apply (list_eq_same_length _ _ (N.to_nat z)).
    - rewrite length_app, length_bv_to_bits, length_replicate. lia.
    - rewrite length_bv_to_bits. reflexivity.
    - intros i b1 b2 Hi L R.
      rewrite bv_to_bits_lookup_Some in L. destruct L as [_ ->].
      rewrite bv_sign_extend_unsigned.
      destruct (Nat.lt_ge_cases i (N.to_nat n)) as [Hi_lo | Hi_hi].
      + rewrite lookup_app_l in R; [| rewrite length_bv_to_bits; exact Hi_lo].
        rewrite bv_to_bits_lookup_Some in R. destruct R as [_ ->].
        rewrite bv_wrap_spec_low; [| split; [lia | rewrite <- N_nat_Z; lia]].
        unfold bv_signed.
        rewrite bv_swrap_spec; [| lia].
        case_bool_decide as Hlt.
        * reflexivity.
        * f_equal. rewrite <- N_nat_Z in *; lia.
      + rewrite lookup_app_r in R; [| rewrite length_bv_to_bits; exact Hi_hi].
        rewrite length_bv_to_bits in R.
        apply lookup_replicate_1 in R. destruct R as [-> _].
        rewrite bv_wrap_spec_low; [| split; [lia | rewrite <- N_nat_Z; lia]].
        unfold bv_signed.
        rewrite bv_swrap_spec; [| lia].
        case_bool_decide as Hlt.
        * exfalso. rewrite <- N_nat_Z in Hlt. lia.
        * destruct (decide (n = 0%N)) as [-> | Hn0].
          -- assert (Hbits0 : bv_to_bits x = []).
             { apply nil_length_inv. rewrite length_bv_to_bits. reflexivity. }
             rewrite Hbits0. cbn.
             apply Z.testbit_neg_r. lia.
          -- assert (Hn0_nat : 0 < N.to_nat n).
             { destruct n as [|p]; [contradiction |]. rewrite positive_N_nat. apply Pos2Nat.is_pos. }
             assert (Hhd : nth 0 (rev (bv_to_bits x)) false = hd false (rev (bv_to_bits x))).
             { destruct (rev (bv_to_bits x)); reflexivity. }
             rewrite <- Hhd.
             rewrite rev_nth; [| rewrite length_bv_to_bits; lia].
             rewrite length_bv_to_bits.
             symmetry.
             apply nth_lookup_Some.
             rewrite bv_to_bits_lookup_Some.
             split; [lia | f_equal; rewrite <- N_nat_Z; lia].
  Qed.

  Lemma sign_extend_abst : ∀ {n : N} {x : bv n} {z : N} h,
    (n ≤ z)%N →
    B.le (B.α (bv_sign_extend z x)) (sign_extend h (B.α (bv_to_bvn x)) (I.α (Z.of_N z))).
  Proof.
    intros n x z h Hnz.
    assert (Hn_le : N.to_nat n ≤ N.to_nat z).
    { apply N2Z.inj_le in Hnz. rewrite <- (N2Nat.id n), <- (N2Nat.id z), !nat_N_Z in Hnz. lia. }
    unfold I.α, sign_extend. cbn.
    assert (Positive : (Z.of_N z <? 0)%Z = false) by (destruct z; reflexivity).
    rewrite Positive, Nat.sub_diag.
    destruct h; cbn.
    - apply BP.le_top.
    - rewrite N_to_nat_via_Z.
      unfold sign_extend_to_width.
      rewrite (B.abstract_bvs x). cbn [proj1_sig].
      rewrite map_fold_singleton, B.join_id.
      unfold sign_extend_one_width.
      destruct (decide (length (map from_bool (bv_to_bits x)) ≤ N.to_nat z)) as [Hd | Hd].
      + assert (Heq : B.α (bv_sign_extend z x) =
                      B.Bvs ({[N.to_nat z := map from_bool (bv_to_bits x) ++
                               replicate (N.to_nat z - length (map from_bool (bv_to_bits x)))
                                 (match rev (map from_bool (bv_to_bits x)) with s :: _ => s | [] => B0 end)]}
                             ↾ sign_extend_one_width_valid _ _ _ Hd)).
        { rewrite B.abstract_bvs. f_equal. apply subset_eq_compat.
          rewrite bv_sign_extend_bits; [| exact Hnz].
          rewrite map_app, fmap_replicate.
          rewrite length_map, length_bv_to_bits.
          rewrite <- map_rev.
          destruct (rev (bv_to_bits x)); reflexivity. }
        rewrite Heq. apply BP.le_refl.
      + exfalso. apply Hd. rewrite (length_map from_bool), length_bv_to_bits. exact Hn_le.
  Qed.

  (** The keys of the underlying gmap are the possible widths of the abstract
      bitvector, so [bits_length] is the join of [I.α (Z.of_nat w)] over every
      width [w] present in the map. *)
  Definition bits_length (b : B.t) : I.t :=
    match b with
    | B.Top   => nonneg_top
    | B.Bvs m =>
        map_fold (λ (w : nat) (_ : list ubit) acc,
          I.join (I.α (Z.of_nat w)) acc) I.bot (`m)
    end.

  Lemma bits_length_abst : ∀ {n : N} {x : bv n},
    bits_length (B.α (bv_to_bvn x)) = I.α (Z.of_N n).
  Proof.
    intros n x.
    rewrite B.abstract_bvs.
    unfold bits_length. cbn [proj1_sig].
    rewrite map_fold_singleton, I.join_id.
    rewrite N_nat_Z. reflexivity.
  Qed.

End Ops.
