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

From stdpp Require Import base.

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
