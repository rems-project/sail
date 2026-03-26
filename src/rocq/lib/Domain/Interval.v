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

From Stdlib Require Import Lia.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import ZArith.

From stdpp Require Import base.

From Sail Require Import Domain.Lattice.
From Sail Require Import OptionUtil.
From Sail Require Import Tactics.

Module Dom <: DOMAIN BinInt.Z.
  Definition Low_high_order (i : option Z * option Z) : Prop :=
    match i with
    | (Some l, Some h) => (l <= h)%Z
    | _ => True
    end.

  Definition endpoints := { i : option Z * option Z | Low_high_order i }.

  Inductive interval : Set :=
    | Empty : interval
    | Ends  : endpoints → interval.

  Definition t := interval.

  Definition low (i : endpoints) : option Z := fst (proj1_sig i).

  Definition high (i : endpoints) : option Z := snd (proj1_sig i).

  Definition extend (op : Z → Z → bool) (end₀ end₁ : option Z) : option Z :=
    match (end₀, end₁) with
    | (Some e₀, Some e₁) => if op e₀ e₁ then end₀ else end₁
    | _ => None
    end.

  Lemma join_low_high : ∀ i₀ i₁,
    Low_high_order (extend Z.ltb (low i₀) (low i₁), extend Z.gtb (high i₀) (high i₁)).
  Proof.
    intros i₀ i₁.
    destruct i₀ as ((l₀, h₀), LH₀).
    destruct i₁ as ((l₁, h₁), LH₁).
    unfold Low_high_order in LH₀, LH₁.
    destruct l₀ as [ l₀ |]; destruct h₀ as [ h₀ |]; destruct l₁ as [ l₁ |]; destruct h₁ as [ h₁ |];
    cbn; destruct_match; try reflexivity.
    reintros ? H1 ? H2.
    destruct (l₀ <? l₁)%Z eqn : ?; destruct (h₀ >? h₁)%Z eqn : ?; inversion H1; inversion H2; lia.
  Qed.

  Lemma low_high_refl : ∀ (n : Z), Low_high_order (Some n, Some n).
  Proof. intros n; unfold Low_high_order; lia. Qed.

  Definition join (i₀ i₁ : interval) : interval :=
    match (i₀, i₁) with
    | (Empty, Empty) => Empty
    | (Empty, Ends i) => Ends i
    | (Ends i, Empty) => Ends i
    | (Ends i₀, Ends i₁) =>
        Ends (exist _ (extend Z.ltb (low i₀) (low i₁), extend Z.gtb (high i₀) (high i₁)) (join_low_high i₀ i₁))
    end.

  Lemma low_high_inf : Low_high_order (None, None).
  Proof. unfold Low_high_order; reflexivity. Qed.

  Lemma low_high_plus_inf : ∀ (n : Z), Low_high_order (Some n, None).
  Proof. intros; unfold Low_high_order; reflexivity. Qed.

  Lemma low_high_neg_inf : ∀ (n : Z), Low_high_order (None, Some n).
  Proof. intros; unfold Low_high_order; reflexivity. Qed.

  Lemma low_high_le : ∀ (l h : Z) (P : (l <= h)%Z), Low_high_order (Some l, Some h).
  Proof.
    intros l h P.
    unfold Low_high_order.
    exact P.
  Qed.

  Definition meet (i₀ i₁ : interval) : interval :=
    match (i₀, i₁) with
    | (Empty, _) => Empty
    | (_, Empty) => Empty
    | (Ends i₀, Ends i₁) =>
        let l := option_join Z.max (low i₀) (low i₁) in
        let h := option_join Z.min (high i₀) (high i₁) in
        match (l, h) with
        | (None, None) => Ends (exist _ (None, None) low_high_inf)
        | (Some l, None) => Ends (exist _ (Some l, None) (low_high_plus_inf l))
        | (None, Some h) => Ends (exist _ (None, Some h) (low_high_neg_inf h))
        | (Some l, Some h) =>
            match ZArith_dec.Z_le_dec l h with
            | left P => Ends (exist _ (Some l, Some h) (low_high_le l h P))
            | right _ => Empty
            end
        end
    end.

  Definition bot := Empty.
  Definition top := Ends (exist _ (None, None) low_high_inf).

  Lemma join_id : ∀ x, join x bot = x.
  Proof.
    intros x.
    destruct x as [| [([lx |], [hx |]) LHx]]; reflexivity.
  Qed.

  Lemma meet_id : ∀ x, meet x top = x.
  Proof.
    intros x.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; try reflexivity.
    all: unfold Low_high_order in LHx.
    destruct_match; [ idtac | lia ].
    all: f_equal; apply subset_eq_compat; reflexivity.
  Qed.

  Lemma join_comm : ∀ x y, join x y = join y x.
  Proof.
    intros x y.
    destruct x as [| [([lx |], [hx |]) LHx]];
    destruct y as [| [([ly |], [hy |]) LHy]].
    all: unfold meet, join, low, high; cbn.
    all: destruct_match.
    all: repeat (
      lazymatch goal with
      | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H
      | [ H : Ends _ = Ends _ |- _ ] => inversion H; clear H
      | [ H : Low_high_order _ |- _ ] => unfold Low_high_order in H; cbn in H
      | [ |- Ends _ = Ends _ ] => f_equal; apply subset_eq_compat
      | [ |- (_, _) = (_, _) ] => f_equal
      | [ |- Some _ = Some _ ] => f_equal
      end
    ).
    all: destruct_match; try f_equal; lia + reflexivity.
  Qed.

  Lemma join_Empty_l : ∀ {x}, join Empty x = x.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma join_Empty_r : ∀ {x}, join x Empty = x.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma join_assoc : ∀ x y z, join x (join y z) = join (join x y) z.
  Proof.
    intros x y z.
    destruct x as [| [([lx |], [hx |]) LHx]];
    destruct y as [| [([ly |], [hy |]) LHy]];
    destruct z as [| [([lz |], [hz |]) LHz]].
    all: try (repeat (try rewrite join_Empty_l; try rewrite join_Empty_r); reflexivity).
    all: unfold join, low, high; cbn; f_equal; apply subset_eq_compat.
    all: destruct_match_goal; intros.
    all: try discriminate.
    all: repeat (
      lazymatch goal with
      | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H
      | [ H : Low_high_order _ |- _ ] => unfold Low_high_order in H; cbn in H
      | [ |- (_, _) = (_, _) ] => f_equal
      | [ |- Some _ = Some _ ] => f_equal
      end
    ).
    all: lia.
  Qed.

  Lemma meet_comm : ∀ x y, meet x y = meet y x.
  Proof.
    intros x y.
    destruct x as [| [([lx |], [hx |]) LHx]];
    destruct y as [| [([ly |], [hy |]) LHy]].
    all: unfold meet, low, high; cbn; try reflexivity.
    all: destruct_match_goal; intros.
    all: try (lia + reflexivity).
    all: f_equal; apply subset_eq_compat.
    all: repeat (
      lazymatch goal with
      | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H
      | [ H : Low_high_order _ |- _ ] => unfold Low_high_order in H; cbn in H
      | [ |- (_, _) = (_, _) ] => f_equal
      | [ |- Some _ = Some _ ] => f_equal
      end
    ).
    all: lia.
  Qed.

  Lemma meet_Empty_l : ∀ {x}, meet Empty x = Empty.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma meet_Empty_r : ∀ {x}, meet x Empty = Empty.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma Z_le_dec_left : ∀ x y l, Z_le_dec x y = left l → (x <= y)%Z.
  Proof. intros; assumption. Qed.

  Lemma meet_assoc : ∀ x y z, meet x (meet y z) = meet (meet x y) z.
  Proof.
    intros x y z.
    destruct x as [| x];
    destruct y as [| y];
    destruct z as [| z].
    all: try (repeat (rewrite meet_Empty_l + rewrite meet_Empty_r); reflexivity).
    destruct x as (([lx |], [hx |]), LHx);
    destruct y as (([ly |], [hy |]), LHy);
    destruct z as (([lz |], [hz |]), LHz).
    all: unfold Low_high_order in LHx, LHy, LHz.
    all: unfold meet, low, high; cbn.
    all: repeat (
      lazymatch goal with
      | [ |- context [ match Z_le_dec ?x ?y with _ => _ end ] ] =>
          destruct (Z_le_dec x y) eqn : ?C; cbn
      | [ H : Z_le_dec _ _ = left _ |- _ ] => apply Z_le_dec_left in H
      end);
      try (lia + reflexivity).
    all: f_equal; apply subset_eq_compat; f_equal; f_equal.
    all: apply Z.max_assoc + apply Z.min_assoc.
  Qed.

  Lemma absorption_join_meet : ∀ x y, join x (meet x y) = x.
  Proof.
    intros x y.
    destruct x as [| [(lx, hx) LHx]]; destruct y as [| [(ly, hy) LHy]]; try reflexivity.
    destruct lx as [lx' |] ; destruct hx as [hx |]; destruct ly as [ly |]; destruct hy as [hy |].
    all: try (cbn; destruct_match; f_equal; apply subset_eq_compat; reflexivity).
    all: try (unfold meet, join, high, low; destruct_match_goal; cbn; try (intros; reflexivity + discriminate)).
    all: intros; f_equal; apply subset_eq_compat.
    inversion C2; cbn.
    all: unfold Low_high_order in LHx, LHy.
    all: destruct e as (([le |], [he |]), IHe) eqn : E; unfold Low_high_order in IHe.
    all: f_equal; destruct_match_goal; cbn; intros; try reflexivity; f_equal.
    all: repeat (
      lazymatch goal with
      | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H
      | [ H : Ends _ = Ends _ |- _ ] => inversion H; clear H
      end
    ).
    all: discriminate + lia.
  Qed.

  Lemma absorption_meet_join : ∀ x y, meet x (join x y) = x.
  Proof.
    intros x y.
    destruct x as [| [([lx |], [hx |]) LHx]]; destruct y as [| [([ly |], [hy |]) LHy ]]; try reflexivity.
    all: unfold meet, join, low, high; cbn.
    all: destruct_match_goal; intros.
    all: repeat (
      lazymatch goal with
      | [ H : Some ?x = Some ?y |- _ ] => inversion H; clear H
      | [ H : Ends _ = Ends _ |- _ ] => inversion H; clear H
      | [ H : Low_high_order _ |- _ ] => unfold Low_high_order in H; cbn in H
      | [ |- Ends _ = Ends _ ] => f_equal; apply subset_eq_compat
      | [ |- (_, _) = (_, _) ] => f_equal
      | [ |- Some _ = Some _ ] => f_equal
      end
    ).
    all: discriminate + lia.
  Qed.

  Definition low_leb (x y : option Z) : bool :=
    match (x, y) with
    | (None, _) => true
    | (_, None) => false
    | (Some x, Some y) => (x <=? y)%Z
    end.

  Definition high_leb (x y : option Z) : bool :=
    match (x, y) with
    | (_, None) => true
    | (None, _) => false
    | (Some x, Some y) => (x <=? y)%Z
    end.

  Definition leb (i₀ i₁ : interval) : bool :=
    match (i₀, i₁) with
    | (Empty, _) => true
    | (_, Empty) => false
    | (Ends e₀, Ends e₁) => low_leb (low e₁) (low e₀) && high_leb (high e₀) (high e₁)
    end.

  Definition le (i₀ i₁ : interval) : Prop := i₁ = join i₀ i₁.

  Lemma leb_le_h1 : ∀ x y, Some y = (if (x <? y)%Z then Some x else Some y) → (y <= x)%Z.
  Proof.
    intros x y.
    destruct_match; intros H; inversion H; lia.
  Qed.

  Lemma leb_le_h2 : ∀ x y, Some y = (if (x >? y)%Z then Some x else Some y) → (x <= y)%Z.
  Proof.
    intros x y.
    destruct_match; intros H; inversion H; lia.
  Qed.

  Lemma leb_le : ∀ x y, leb x y = true ↔ le x y.
  Proof.
    intros x y.
    split; intros H.
    - unfold le.
      destruct x as [| x]; destruct y as [| y]; try (cbn in H; easy).
      unfold leb, low, high in H.
      rewrite andb_true_iff in H.
      destruct H as [L H].
      unfold join, low, high.
      destruct x as [([lx |], [hx |]) LHx];
      destruct y as [([ly |], [hy |]) LHy].
      all: unfold Low_high_order in LHx, LHy.
      all: cbn in L, H.
      all: cbn; f_equal; apply subset_eq_compat; f_equal; f_equal.
      all: destruct_match; f_equal; lia.
    - unfold le in H.
      destruct x as [| x]; destruct y as [| y]; try (cbn in H; easy).
      unfold join, low, high in H.
      destruct x as [([lx |], [hx |]) LHx];
      destruct y as [([ly |], [hy |]) LHy].
      all: unfold Low_high_order in LHx, LHy.
      all: cbn in H; inversion H; clear H.
      all: repeat (
        lazymatch goal with
        | [ H : Some ?y = (if (?x <? ?y)%Z then Some ?x else Some ?y) |- _ ] => apply leb_le_h1 in H
        | [ H : Some ?y = (if (?x >? ?y)%Z then Some ?x else Some ?y) |- _ ] => apply leb_le_h2 in H
        end
      ).
      all: unfold leb, low, high; cbn; lia.
  Qed.

  Lemma le_join_def : ∀ x y, le x y ↔ y = join x y.
  Proof.
    unfold le.
    reflexivity.
  Qed.

  Definition low_bound (e : endpoints) (n : Z) :=
    match low e with
    | None => True
    | Some m => (m <= n)%Z
    end.

  Definition high_bound (e : endpoints) (n : Z) :=
    match high e with
    | None => True
    | Some m => (n <= m)%Z
    end.

  Definition α (n : Z) : interval := Ends (exist _ (Some n, Some n) (low_high_refl n)).
End Dom.
