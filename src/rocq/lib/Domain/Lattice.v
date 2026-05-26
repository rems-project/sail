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

From Stdlib Require Import ZArith.

From stdpp Require Import base.
From stdpp Require Import bitvector.definitions.

Module Type CONCRETE.
  Parameter t : Set.
End CONCRETE.

Module Type DOMAIN (C : CONCRETE).
  Parameter t : Set.

  Parameter join : t → t → t.
  Parameter meet : t → t → t.
  Parameter top : t.
  Parameter bot : t.

  Notation "⊤" := top.
  Notation "⊥" := bot.

  Infix "⊔" := join (no associativity, at level 50).
  Infix "⊓" := meet (no associativity, at level 40).

  Parameter join_comm : ∀ x y, x ⊔ y = y ⊔ x.
  Parameter join_assoc : ∀ x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.

  Parameter meet_comm : ∀ x y, x ⊓ y = y ⊓ x.
  Parameter meet_assoc : ∀ x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.

  Parameter absorption_join_meet : ∀ x y, x ⊔ (x ⊓ y) = x.
  Parameter absorption_meet_join : ∀ x y, x ⊓ (x ⊔ y) = x.

  Parameter join_id : ∀ x, x ⊔ ⊥ = x.
  Parameter meet_id : ∀ x, x ⊓ ⊤ = x.

  Parameter leb : t → t → bool.
  Parameter le : t → t → Prop.

  Infix "⊑" := le (right associativity, at level 70).

  Parameter leb_le : ∀ x y, leb x y = true ↔ x ⊑ y.
  Parameter le_join_def : ∀ x y, x ⊑ y ↔ y = x ⊔ y.

  Parameter α : C.t → t.
End DOMAIN.

Module DomainProperties (C : CONCRETE) (D : DOMAIN C).
  Import D.

  (** [le] can be equivalently defined in terms of [meet] *)
  Lemma le_meet_def : ∀ x y, x ⊑ y ↔ x = x ⊓ y.
  Proof.
    intros x y.
    rewrite le_join_def.
    split.
    - intros J.
      assert (S : x = x ⊓ (x ⊔ y)). { exact (eq_sym (absorption_meet_join x y)). }
      rewrite <- J in S.
      exact S.
    - intros M.
      assert (S : y = y ⊔ (y ⊓ x)). { exact (eq_sym (absorption_join_meet y x)). }
      rewrite meet_comm, <- M, join_comm in S.
      exact S.
  Qed.

  Lemma le_top : ∀ x, x ⊑ ⊤.
  Proof. intros. rewrite le_meet_def, meet_id. reflexivity. Qed.

  Lemma le_bot : ∀ x, ⊥ ⊑ x.
  Proof. intros. rewrite le_join_def, join_comm, join_id. reflexivity. Qed.

  Lemma join_idem : ∀ x, x ⊔ x = x.
  Proof.
    intros x.
    rewrite <- (absorption_join_meet x (x ⊔ x)) at 3.
    rewrite absorption_meet_join.
    reflexivity.
  Qed.

  Lemma meet_idem : ∀ x, x ⊓ x = x.
  Proof.
    intros x.
    rewrite <- (absorption_meet_join x (x ⊓ x)) at 3.
    rewrite absorption_join_meet.
    reflexivity.
  Qed.

  Lemma le_refl : ∀ x, x ⊑ x.
  Proof.
    intros x.
    rewrite le_join_def.
    exact (eq_sym (join_idem x)).
  Qed.

  Lemma le_trans : ∀ x y z, x ⊑ y → y ⊑ z → x ⊑ z.
  Proof.
    intros x y z.
    repeat rewrite le_join_def; intros XY YZ.
    rewrite YZ.
    rewrite join_assoc.
    rewrite <- XY.
    reflexivity.
  Qed.

  Lemma le_antisym : ∀ x y, x ⊑ y → y ⊑ x → x = y.
  Proof.
    intros x y L R.
    rewrite le_join_def in *.
    rewrite L.
    rewrite R at 1.
    exact (join_comm y x).
  Qed.

  Lemma leb_bot : ∀ x, leb x ⊥ = true ↔ x = ⊥.
  Proof.
    intros x.
    split; intros H.
    - rewrite leb_le, le_join_def, join_id in H.
      exact (eq_sym H).
    - rewrite H, leb_le.
      apply le_refl.
  Qed.
End DomainProperties.

Module Type SAIL_INT.
  Parameter t : Set.

  (** A [SAIL_INT] domain is always an abstraction of Rocq's integer [Z] type. *)
  Parameter α : Z → t.

  Parameter negate : t -> t.
  Parameter negate_abst : ∀ {x}, α (-x) = negate (α x).
  Parameter negate_negate : ∀ {x}, negate (negate x) = x.

  Parameter add : t → t → t.
  Parameter add_abst : ∀ {x y}, α (x + y) = add (α x) (α y).
  Parameter add_comm : ∀ {x y}, add x y = add y x.
  Parameter add_assoc : ∀ {x y z}, add x (add y z) = add (add x y) z.

  Parameter sub : t → t → t.
  Parameter sub_abst : ∀ {x y}, α (x - y) = sub (α x) (α y).

  Parameter mult : t → t → t.
  Parameter mult_abst : ∀ {x y}, α (x * y) = mult (α x) (α y).

  Parameter max : t → t → t.
  Parameter max_abst : ∀ {x y}, α (Z.max x y) = max (α x) (α y).

  Parameter min : t → t → t.
  Parameter min_abst : ∀ {x y}, α (Z.min x y) = min (α x) (α y).

  Parameter abs : t → t.
  Parameter abs_abst : ∀ {x}, α (Z.abs x) = abs (α x).

  (** Truncating division (round towards zero) *)
  Parameter tdiv : t → t → t.
  Parameter tdiv_abst : ∀ {x y}, α (Z.quot x y) = tdiv (α x) (α y).

  Parameter tmod : t → t → t.
  Parameter tmod_abst : ∀ {x y}, α (Z.rem x y) = tmod (α x) (α y).

  (** Flooring division (floor towards -∞) *)
  Parameter fdiv : t → t → t.
  Parameter fdiv_abst : ∀ {x y}, α (Z.div x y) = fdiv (α x) (α y).

  Parameter fmod : t → t → t.
  Parameter fmod_abst : ∀ {x y}, α (Z.modulo x y) = fmod (α x) (α y).

  (** Euclidian division *)
  Parameter ediv : t → t → t.
  Parameter ediv_abst : ∀ {x y}, α (fst (Z.div_eucl x y)) = ediv (α x) (α y).

  Parameter emod : t → t → t.
  Parameter emod_abst : ∀ {x y}, α (snd (Z.div_eucl x y)) = emod (α x) (α y).
End SAIL_INT.

Module Type SAIL_BITS.
  Parameter t : Set.

  Parameter α : bvn → t.

  Parameter le : t → t → Prop.

  Parameter not : t → t.
  Parameter not_abst : ∀ {n} {x : bv n}, α (bv_to_bvn (bv_not x)) = not (α (bv_to_bvn x)).

  Parameter add : t → t → t.
  Parameter add_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (x + y)) = add (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  Parameter negate : t → t.
  Parameter negate_abst : ∀ {n} {x : bv n}, α (bv_to_bvn (- x)) = negate (α (bv_to_bvn x)).

  Parameter sub : t → t → t.
  Parameter sub_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (x - y)) = sub (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  Parameter and : t → t → t.
  Parameter and_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (bv_and x y)) = and (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  Parameter or : t → t → t.
  Parameter or_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (bv_or x y)) = or (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  Parameter xor : t → t → t.
  Parameter xor_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (bv_xor x y)) = xor (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  Parameter append : t → t → t.
  Parameter append_abst : ∀ {n m} {x : bv n} {y : bv m},
    α (bv_to_bvn (bv_concat (n + m) x y)) = append (α (bv_to_bvn x)) (α (bv_to_bvn y)).

  (** <<slice bv s n>> extracts a bitvector of length <<n>> from <<bv>>, starting at index <<s>>. *)
  Parameter slice : t → N → N → t.
  Parameter slice_abst : ∀ {n s m} {x : bv n}, α (bv_extract s m x) = slice (α x) s m.
End SAIL_BITS.

Module Type SAIL_BITS_INT (Bits : SAIL_BITS) (Int : SAIL_INT).
  Parameter unsigned : Bits.t → Int.t.
  Parameter unsigned_abst : ∀ {n} {x : bv n},
    Int.α (bv_unsigned x) = unsigned (Bits.α x).

  Parameter signed : Bits.t → Int.t.
  Parameter signed_abst : ∀ {n} {x : bv n},
    Int.α (bv_signed x) = signed (Bits.α x).

  (** Generate a bitvector containing all zeros.

      If the interval is very wide, then this might produce a huge
      number of bitvector widths. The first argument therefore
      determines the maximum amount of bitvector widths that can be
      generated, otherwise we generate [Bits.⊤] *)
  Parameter zeros : nat → Int.t → Bits.t.
  Parameter zeros_abst : ∀ {n : N} h,
    Bits.le (Bits.α (bv_0 n)) (zeros h (Int.α (Z.of_N n))).

  (** Generate a bitvector containing all ones.

      See [zeros]. *)
  Parameter ones : nat → Int.t → Bits.t.
  Parameter ones_abst : ∀ {n} h,
    Bits.le (Bits.α (bv_not (bv_0 n))) (ones h (Int.α (Z.of_N n))).

  (** <<zero_extend h b n>> extends b to length n.

      The heuristic logic is the same as for zeros. If the number of
      possible bitvector widths would be greater than <<h>>, then
      return [Bits.⊤]. *)
  Parameter zero_extend : nat → Bits.t → Int.t → Bits.t.
  Parameter zero_extend_abst : ∀ {n : N} {x : bv n} {z : N} h,
    (n ≤ z)%N →
    Bits.le (Bits.α (bv_zero_extend z x)) (zero_extend h (Bits.α x) (Int.α (Z.of_N z))).

  Parameter sign_extend : nat → Bits.t → Int.t → Bits.t.
  Parameter sign_extend_abst : ∀ {n : N} {x : bv n} {z : N} h,
    (n ≤ z)%N →
    Bits.le (Bits.α (bv_sign_extend z x)) (sign_extend h (Bits.α x) (Int.α (Z.of_N z))).

  Parameter count_leading_zeros : Bits.t → Int.t.

  Parameter count_trailing_zeros : Bits.t → Int.t.
End SAIL_BITS_INT.
