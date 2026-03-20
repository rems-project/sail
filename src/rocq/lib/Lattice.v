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

From Stdlib Require Import Bool.
From Stdlib Require Import Eqdep.
From Stdlib Require Import Lia.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Logic.ProofIrrelevance.
From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.
From Stdlib Require Sets.Ensembles.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From stdpp Require Import base.
From stdpp Require Import gmap.
From stdpp Require Import list.

From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import OptionUtil.
From Sail Require Import Tactics.
From Sail Require Ast.

Import ListNotations.

Module Type CONCRETE.
  Parameter t : Type.
End CONCRETE.

Module Type DOMAIN (C : CONCRETE).
  Parameter t : Type.

  Parameter join : t -> t -> t.
  Parameter meet : t -> t -> t.
  Parameter top : t.
  Parameter bot : t.

  Notation "⊤" := top.
  Notation "⊥" := bot.

  Infix "⊔" := join (no associativity, at level 50).
  Infix "⊓" := meet (no associativity, at level 40).

  Parameter join_comm : forall x y, x ⊔ y = y ⊔ x.
  Parameter join_assoc : forall x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.

  Parameter meet_comm : forall x y, x ⊓ y = y ⊓ x.
  Parameter meet_assoc : forall x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.

  Parameter absorption_join_meet : forall x y, x ⊔ (x ⊓ y) = x.
  Parameter absorption_meet_join : forall x y, x ⊓ (x ⊔ y) = x.

  Parameter join_id : forall x, x ⊔ ⊥ = x.
  Parameter meet_id : forall x, x ⊓ ⊤ = x.

  Parameter leb : t -> t -> bool.
  Parameter le : t -> t -> Prop.

  Infix "⊑" := le (right associativity, at level 70).

  Parameter leb_le : forall x y, leb x y = true <-> x ⊑ y.
  Parameter le_join_def : forall x y, x ⊑ y <-> y = x ⊔ y.

  Parameter γ : t -> Ensembles.Ensemble C.t.
  Parameter α : C.t -> t.

  Infix "⊆" := (Ensembles.Included C.t) (right associativity, at level 70).

  Parameter galois : forall (x : C.t) y, α x ⊑ y <-> Ensembles.Singleton C.t x ⊆ γ y.
End DOMAIN.

Module DomainProperties (C : CONCRETE) (D : DOMAIN C).
  Import D.

  (** [le] can be equivalently defined in terms of [meet] *)
  Lemma le_meet_def : forall x y, x ⊑ y <-> x = x ⊓ y.
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

  Lemma join_idem : forall x, x ⊔ x = x.
  Proof.
    intros x.
    rewrite <- (absorption_join_meet x (x ⊔ x)) at 3.
    rewrite absorption_meet_join.
    reflexivity.
  Qed.

  Lemma meet_idem : forall x, x ⊓ x = x.
  Proof.
    intros x.
    rewrite <- (absorption_meet_join x (x ⊓ x)) at 3.
    rewrite absorption_join_meet.
    reflexivity.
  Qed.

  Lemma le_refl : forall x, x ⊑ x.
  Proof.
    intros x.
    rewrite le_join_def.
    exact (eq_sym (join_idem x)).
  Qed.

  Lemma le_trans : forall x y z, x ⊑ y -> y ⊑ z -> x ⊑ z.
  Proof.
    intros x y z.
    repeat rewrite le_join_def; intros XY YZ.
    rewrite YZ.
    rewrite join_assoc.
    rewrite <- XY.
    reflexivity.
  Qed.

  Lemma le_antisym : forall x y, x ⊑ y -> y ⊑ x -> x = y.
  Proof.
    intros x y L R.
    rewrite le_join_def in *.
    rewrite L.
    rewrite R at 1.
    exact (join_comm y x).
  Qed.

  Lemma leb_bot : forall x, leb x ⊥ = true <-> x = ⊥.
  Proof.
    intros x.
    split; intros H.
    - rewrite leb_le, le_join_def, join_id in H.
      exact (eq_sym H).
    - rewrite H, leb_le.
      apply le_refl.
  Qed.
End DomainProperties.

Module Interval <: DOMAIN BinInt.Z.
  Definition Low_high_order (i : option Z * option Z) : Prop :=
    match i with
    | (Some l, Some h) => (l <= h)%Z
    | _ => True
    end.

  Definition endpoints := { i : option Z * option Z | Low_high_order i }.

  Inductive interval : Set :=
    | Empty : interval
    | Ends  : endpoints -> interval.

  Definition t := interval.

  Definition low (i : endpoints) : option Z := fst (proj1_sig i).

  Definition high (i : endpoints) : option Z := snd (proj1_sig i).

  Definition extend (op : Z -> Z -> bool) (end₀ end₁ : option Z) : option Z :=
    match (end₀, end₁) with
    | (Some e₀, Some e₁) => if op e₀ e₁ then end₀ else end₁
    | _ => None
    end.

  Lemma join_low_high : forall i₀ i₁,
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

  Lemma low_high_refl : forall (n : Z), Low_high_order (Some n, Some n).
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

  Lemma low_high_plus_inf : forall (n : Z), Low_high_order (Some n, None).
  Proof. intros; unfold Low_high_order; reflexivity. Qed.

  Lemma low_high_neg_inf : forall (n : Z), Low_high_order (None, Some n).
  Proof. intros; unfold Low_high_order; reflexivity. Qed.

  Lemma low_high_le : forall (l h : Z) (P : (l <= h)%Z), Low_high_order (Some l, Some h).
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

  Lemma join_id : forall x, join x bot = x.
  Proof.
    intros x.
    destruct x as [| [([lx |], [hx |]) LHx]]; reflexivity.
  Qed.

  Lemma meet_id : forall x, meet x top = x.
  Proof.
    intros x.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; try reflexivity.
    all: unfold Low_high_order in LHx.
    destruct_match; [ idtac | lia ].
    all: f_equal; apply subset_eq_compat; reflexivity.
  Qed.

  Lemma join_comm : forall x y, join x y = join y x.
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

  Lemma join_Empty_l : forall {x}, join Empty x = x.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma join_Empty_r : forall {x}, join x Empty = x.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma join_assoc : forall x y z, join x (join y z) = join (join x y) z.
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

  Lemma meet_comm : forall x y, meet x y = meet y x.
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

  Lemma meet_Empty_l : forall {x}, meet Empty x = Empty.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma meet_Empty_r : forall {x}, meet x Empty = Empty.
  Proof.
    destruct x as [| [([lx |], [hx |]) LHx]]; cbn; reflexivity.
  Qed.

  Lemma Z_le_dec_left : forall x y l, Z_le_dec x y = left l -> (x <= y)%Z.
  Proof. intros; assumption. Qed.

  Lemma meet_assoc : forall x y z, meet x (meet y z) = meet (meet x y) z.
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

  Lemma absorption_join_meet : forall x y, join x (meet x y) = x.
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

  Lemma absorption_meet_join : forall x y, meet x (join x y) = x.
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

  Lemma leb_le_h1 : forall x y, Some y = (if (x <? y)%Z then Some x else Some y) -> (y <= x)%Z.
  Proof.
    intros x y.
    destruct_match; intros H; inversion H; lia.
  Qed.

  Lemma leb_le_h2 : forall x y, Some y = (if (x >? y)%Z then Some x else Some y) -> (x <= y)%Z.
  Proof.
    intros x y.
    destruct_match; intros H; inversion H; lia.
  Qed.

  Lemma leb_le : forall x y, leb x y = true <-> le x y.
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

  Lemma le_join_def : forall x y, le x y <-> y = join x y.
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

  Definition γ (i : interval) : Ensembles.Ensemble Z :=
    match i with
    | Empty => Ensembles.Empty_set Z
    | Ends e => fun n => low_bound e n /\ high_bound e n
    end.

  Definition α (n : Z) : interval := Ends (exist _ (Some n, Some n) (low_high_refl n)).

  Infix "⊑" := le (right associativity, at level 70).
  Infix "⊆" := (Ensembles.Included Z) (right associativity, at level 70).

  Lemma Singleton_eq : forall x y, Ensembles.Singleton Z x y -> y = x.
  Proof. intros ? ? S; destruct S; reflexivity. Qed.

  Lemma proj1_exist : forall {A} (x : A -> Prop) (y : A) (z : x y), proj1_sig (exist x y z) = y.
  Proof. intros; cbn; reflexivity. Qed.

  Lemma galois : forall (x : Z) (y : interval), α x ⊑ y <-> Ensembles.Singleton Z x ⊆ γ y.
  Proof.
    intros x y.
    split.
    - intros Alpha.
      destruct y as [| e]; try discriminate.
      unfold le, join, α in Alpha.
      inversion Alpha as [H].
      clear Alpha.
      unfold γ, Ensembles.Included, In.
      intros ? S.
      apply Singleton_eq in S; subst.
      split.
      + unfold low_bound, low.
        rewrite proj1_exist.
        cbn.
        destruct (fst (proj1_sig e)); try reflexivity.
        destruct (x <? z)%Z eqn : ?; lia.
      + unfold high_bound, high.
        rewrite proj1_exist.
        cbn.
        destruct (snd (proj1_sig e)); try reflexivity.
        destruct (x >? z)%Z eqn : ?; lia.
    - intros Gamma.
      unfold Ensembles.Included, γ in Gamma.
      specialize (Gamma x (Ensembles.In_singleton Z x)).
      unfold In in Gamma.
      destruct y as [| e]; try discriminate.
      + destruct Gamma.
      + destruct Gamma as [Low High].
        unfold α, le, join.
        f_equal.
        destruct e as ((l, h), LH).
        apply subset_eq_compat.
        destruct l as [ l' |]; destruct h as [ h' |];
        unfold low_bound, low, high_bound, high in *; cbn in *;
        f_equal; destruct_match; lia + reflexivity.
  Qed.
End Interval.

Module BitList.
  Definition t := list Bit.bit.
End BitList.

Module AbsBV <: DOMAIN BitList.
  Import Bit.Three.

  Definition valid (m : gmap nat (list ubit)) : Prop :=
    ∀ n, match m !! n with
         | Some xs => length xs = n
         | None    => True
         end.

  Inductive bvset : Set :=
    | Top : bvset
    | Bvs : { m : gmap nat (list ubit) | valid m } -> bvset.

  Definition t : Set := bvset.

  Definition top := Top.

  Notation "⊤" := Top.

  Lemma empty_is_valid : valid ∅.
  Proof. unfold valid; intros; rewrite lookup_empty; reflexivity. Qed.

  Definition bot : t := Bvs (∅ ↾ empty_is_valid).

  Notation "⊥" := bot.

  Definition join_aux (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    merge (option_join (zip_with bit_join)) x y.

  Lemma join_aux_preserves_valid : ∀ {x y : gmap nat (list ubit)}, valid x -> valid y -> valid (join_aux x y).
  Proof.
    intros x y Vx Vy.
    unfold valid, join_aux in *; intros n.
    specialize (Vx n).
    specialize (Vy n).
    rewrite lookup_merge.
    destruct (x !! n) as [xs |]; destruct (y !! n) as [ys |]; cbn.
    - rewrite length_zip_with, Vx, Vy, Nat.min_id. reflexivity.
    - exact Vx.
    - exact Vy.
    - reflexivity.
  Qed.

  Lemma join_aux_comm : ∀ {x y : gmap nat (list ubit)}, join_aux x y = join_aux y x.
  Proof.
    intros x y.
    unfold join_aux.
    apply merge_comm.
    intros n.
    apply option_join_comm.
    intros xbs.
    induction xbs as [| xb xbs IH]; intros ys; destruct ys as [| yb ybs]; try reflexivity.
    cbn [zip_with]; f_equal; [ apply bit_join_comm | apply IH ].
  Qed.

  Lemma join_aux_assoc : ∀ {x y z : gmap nat (list ubit)}, join_aux x (join_aux y z) = join_aux (join_aux x y) z.
  Proof.
    intros x y z.
    unfold join_aux.
    apply merge_assoc.
    intros n.
    destruct (x !! n) as [xs |]; destruct (y !! n) as [ys |]; destruct (z !! n) as [zs |]; try reflexivity.
    clear x y z n.
    cbn; f_equal.
    revert xs zs.
    induction ys as [| y ys IH]; intros xs zs; destruct xs as [| x xs]; destruct zs as [| z zs]; try reflexivity.
    cbn [zip_with]; f_equal; [ apply bit_join_assoc | apply IH ].
  Qed.

  Definition join (x y : t) : t :=
    match (x, y) with
    | (⊤, _) => ⊤
    | (_, ⊤) => ⊤
    | (Bvs x, Bvs y) =>
        Bvs (join_aux (`x) (`y) ↾ (join_aux_preserves_valid (proj2_sig x) (proj2_sig y)))
    end.

  Infix "⊔" := join (no associativity, at level 50).

  Lemma join_comm : ∀ x y, x ⊔ y = y ⊔ x.
  Proof.
    intros x y.
    destruct x as [| x]; destruct y as [| y]; try reflexivity.
    unfold join; f_equal; apply subset_eq_compat.
    apply join_aux_comm.
  Qed.

  Lemma join_assoc : ∀ x y z, x ⊔ (y ⊔ z) = (x ⊔ y) ⊔ z.
  Proof.
    intros x y z.
    destruct x as [| x]; destruct y as [| y]; destruct z as [| z]; try reflexivity.
    unfold join; f_equal; apply subset_eq_compat.
    cbn - [join_aux].
    apply join_aux_assoc.
  Qed.

  Definition meet_aux (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    merge (option_bind2 (λ xs ys, option_all $ zip_with bit_meet xs ys)) x y.

  Lemma meet_aux_preserves_valid : ∀ {x y : gmap nat (list ubit)}, valid x -> valid y -> valid (meet_aux x y).
  Proof.
    intros x y Vx Vy.
    unfold valid, meet_aux in *; intros n.
    specialize (Vx n).
    specialize (Vy n).
    rewrite lookup_merge.
    destruct (x !! n) as [xs |]; destruct (y !! n) as [ys |]; try reflexivity; cbn.
    destruct (option_all (zip_with bit_meet xs ys)) eqn : bitwise_meet; try reflexivity.
    apply option_all_length in bitwise_meet.
    rewrite length_zip_with_l_eq, Vx in bitwise_meet; subst; easy.
  Qed.

  Lemma Some_inj : forall {A} {x y : A}, Some x = Some y -> x = y.
  Proof. intros A x y H; inversion H; subst; reflexivity. Qed.

  Lemma option_all_nil : forall {A}, @option_all A [] = Some [].
  Proof. intros; cbn; reflexivity. Qed.

  Lemma option_all_cons_nil : forall {A} (x : option A) xs, option_all (x :: xs) = Some [] -> False.
  Proof.
    intros A x xs.
    rewrite option_all_is_alt.
    destruct x; cbn.
    - destruct (option_all_alt xs); intros; discriminate.
    - intros; discriminate.
  Qed.

  Lemma option_all_cons_cons : forall {A} (x : option A) xs y ys,
    option_all (x :: xs) = Some (y :: ys) -> x = Some y ∧ option_all xs = Some ys.
  Proof.
    intros A x xs y ys.
    repeat rewrite option_all_is_alt in *.
    destruct x; cbn.
    - destruct (option_all_alt xs) eqn : H1; intros H2; inversion H2.
      apply conj; reflexivity.
    - intros; discriminate.
  Qed.

  Lemma option_all_cons_none : forall {A} (x : option A) xs,
    option_all (x :: xs) = None -> x = None ∨ option_all xs = None.
  Proof.
    intros A x xs.
    destruct x as [x |].
    rewrite option_all_is_alt.
    cbn.
    destruct (option_all_alt xs) eqn : H.
    - intros; discriminate.
    - intros. rewrite <- option_all_is_alt in H. tauto.
    - cbn. tauto.
  Qed.

  Lemma option_all_cons : forall {A} (x y : option A) xs ys,
    x = y -> option_all xs = option_all ys -> option_all (x :: xs) = option_all (y :: ys).
  Proof.
    intros A x y xs ys H1 H2.
    subst.
    repeat rewrite option_all_is_alt in *.
    cbn [option_all_alt].
    rewrite H2.
    reflexivity.
  Qed.

  Lemma zip_with_bit_meet_idemp : forall xs, option_all (zip_with bit_meet xs xs) = Some xs.
  Proof.
    induction xs as [| x xs IH].
    - reflexivity.
    - rewrite option_all_is_alt.
      cbn [option_all_alt zip_with].
      rewrite <- option_all_is_alt.
      rewrite IH.
      destruct x; reflexivity.
  Qed.

  Ltac zip_with_empty :=
    repeat (
      lazymatch goal with
      | [ H : context [ zip_with _ [] _ ] |- _ ] => rewrite zip_with_nil_l in H
      | [ H : context [ zip_with _ _ [] ] |- _ ] => rewrite zip_with_nil_r in H
      | [ H : context [ zip_with _ (_ :: _) (_ :: _) ] |- _ ] => cbn [zip_with] in H
      | [ H : context [ option_all [] ] |- _ ] => rewrite option_all_nil in H
      | [ H : Some [] = Some ?x |- _ ] => apply Some_inj in H; subst x
      | [ H : option_all (?x :: ?xs) = Some [] |- _ ] => exfalso; apply (option_all_cons_nil x xs H)
      | [ H : option_all (?x :: ?xs) = Some (?y :: ?ys) |- _ ] => apply option_all_cons_cons in H
      | [ H : option_all (?x :: ?xs) = None |- _ ] => apply option_all_cons_none in H
      | |- context [ zip_with _ [] _ ] => rewrite zip_with_nil_l
      | |- context [ zip_with _ _ [] ] => rewrite zip_with_nil_r
      | |- context [ zip_with _ (_ :: _) (_ :: _) ] => cbn [zip_with]
      end
    );
    try (reflexivity + discriminate).

  Definition meet (x y : t) : t :=
    match (x, y) with
    | (⊤, y) => y
    | (x, ⊤) => x
    | (Bvs x, Bvs y) =>
        Bvs (meet_aux (`x) (`y) ↾ (meet_aux_preserves_valid (proj2_sig x) (proj2_sig y)))
    end.

  Infix "⊓" := meet (no associativity, at level 40).

  Lemma meet_comm : ∀ x y, x ⊓ y = y ⊓ x.
  Proof.
    intros x y.
    destruct x as [| [x Vx]]; destruct y as [| [y Vy]]; try reflexivity.
    unfold meet; f_equal; apply subset_eq_compat.
    unfold meet_aux.
    apply merge_comm.
    intros n.
    unfold proj1_sig.
    destruct (x !! n) as [xs |] eqn : HX; destruct (y !! n) as [ys |] eqn : HY; try reflexivity.
    cbn; f_equal.
    clear Vx HX Vy HY x y n.
    revert ys.
    induction xs as [| x xs IH]; intros ys; destruct ys as [| y ys]; try reflexivity.
    cbn [zip_with]; f_equal; [ apply bit_meet_comm | apply IH ].
  Qed.

  Lemma meet_assoc : ∀ x y z, x ⊓ (y ⊓ z) = (x ⊓ y) ⊓ z.
  Proof.
    intros x y z.
    destruct x as [| [x Vx]];
    destruct y as [| [y Vy]];
    destruct z as [| [z Vz]]; try reflexivity.
    unfold meet; f_equal; apply subset_eq_compat.
    cbn - [meet_aux].
    unfold meet_aux.
    apply merge_assoc.
    intros n.
    destruct (x !! n) as [xs |] eqn : HX;
    destruct (y !! n) as [ys |] eqn : HY;
    destruct (z !! n) as [zs |] eqn : HZ; try reflexivity; cbn.
    - unfold valid in Vx, Vy, Vz.
      specialize (Vx n).
      rewrite HX in Vx.
      specialize (Vy n).
      rewrite HY in Vy.
      specialize (Vz n).
      rewrite HZ in Vz.
      assert (xs_ys_length : length xs = length ys). {
        rewrite Vx, Vy. reflexivity.
      }
      assert (ys_zs_length : length ys = length zs). {
        rewrite Vy, Vz. reflexivity.
      }
      clear HX HY HZ Vx x Vy y Vz z n.
      destruct (option_all (zip_with bit_meet xs ys)) as [xys |] eqn : XY;
      destruct (option_all (zip_with bit_meet ys zs)) as [yzs |] eqn : YZ; cbn.
      + clear xs_ys_length ys_zs_length.
        revert XY YZ.
        revert xs zs xys yzs.
        induction ys as [| y ys IH]; intros xs zs xys yzs XY YZ; zip_with_empty.
        destruct xs as [| x xs]; destruct zs as [| z zs]; destruct xys as [| xy xys]; destruct yzs as [| yz yzs]; zip_with_empty.
        apply option_all_cons.
        * destruct XY as [XY _]; destruct YZ as [YZ _].
          destruct x; destruct y; destruct z; cbn in *;
          inversion XY; inversion YZ; subst; reflexivity.
        * apply IH; tauto.
      + revert XY YZ xs_ys_length ys_zs_length.
        revert xs zs xys.
        induction ys as [| y ys IH]; intros xs zs xys XY YZ xs_ys_length ys_zs_length; zip_with_empty.
        destruct xs as [| x xs]; [ cbn in xs_ys_length; discriminate | idtac ].
        destruct zs as [| z zs]; [ cbn in ys_zs_length; discriminate | idtac ].
        destruct xys as [| xy xys]; zip_with_empty.
        rewrite option_all_is_alt.
        cbn [option_all_alt].
        rewrite <- option_all_is_alt.
        destruct YZ.
        * destruct XY as [XY _];
          destruct x; destruct y; destruct z; cbn in *; inversion XY; discriminate + reflexivity.
        * destruct (bit_meet xy z); try reflexivity.
          rewrite <- (IH xs zs xys); try (easy + cbn in *; lia).
      + revert XY YZ xs_ys_length ys_zs_length.
        revert xs zs yzs.
        induction ys as [| y ys IH]; intros xs zs yzs XY YZ xs_ys_length ys_zs_length; zip_with_empty.
        destruct xs as [| x xs]; [ cbn in xs_ys_length; discriminate | idtac ].
        destruct zs as [| z zs]; [ cbn in ys_zs_length; discriminate | idtac ].
        destruct yzs as [| xy xys]; zip_with_empty.
        rewrite option_all_is_alt.
        cbn [option_all_alt].
        rewrite <- option_all_is_alt.
        destruct XY.
        * destruct YZ as [YZ _];
          destruct x; destruct y; destruct z; cbn in *; inversion YZ; discriminate + reflexivity.
        * destruct (bit_meet x xy); try reflexivity.
          rewrite (IH xs zs xys); try (easy + cbn in *; lia).
      + reflexivity.
    - destruct (option_all (zip_with bit_meet xs ys)); reflexivity.
    - destruct (option_all (zip_with bit_meet ys zs)); reflexivity.
  Qed.

  Lemma absorption_join_meet : ∀ x y, x ⊔ (x ⊓ y) = x.
  Proof.
    intros x y.
    destruct x as [| [x Vx]];
    destruct y as [| [y Vy]]; try reflexivity.
    - unfold meet. unfold join.
      f_equal.
      apply subset_eq_compat.
      cbn.
      apply merge_idemp.
      intros n.
      destruct (x !! n) as [xs |]; try reflexivity.
      cbn; f_equal.
      induction xs as [| x' xs' IH]; try reflexivity.
      cbn [zip_with].
      rewrite IH.
      destruct x'; reflexivity.
    - unfold meet. unfold join.
      f_equal.
      apply subset_eq_compat.
      apply merge_Some; try reflexivity.
      intros n.
      cbn.
      rewrite lookup_merge.
      destruct (x !! n) as [xs |] eqn : HX; destruct (y !! n) as [ys |] eqn : HY; try reflexivity.
      unfold valid in Vx, Vy.
      specialize (Vx n).
      rewrite HX in Vx.
      specialize (Vy n).
      rewrite HY in Vy.
      assert (Len : length xs = length ys). {
        rewrite Vx, Vy. reflexivity.
      }
      clear HX HY Vx Vy x y n.
      cbn.
      destruct (option_all (zip_with bit_meet xs ys)) as [zs |] eqn : H; try reflexivity.
      revert H Len.
      revert ys zs.
      induction xs as [| x xs IH].
      + intros; reflexivity.
      + intros ys zs H Len.
        destruct ys as [| y ys]; destruct zs as [| z zs]; zip_with_empty.
        repeat f_equal.
        * destruct H as [H _].
          destruct x, y, z; cbn in *; inversion H; reflexivity + discriminate.
        * specialize (IH ys zs).
          destruct H as [_ H].
          apply IH in H.
          ** apply Some_inj in H; exact H.
          ** cbn in Len; lia.
  Qed.

  Lemma absorption_meet_join : ∀ x y, x ⊓ (x ⊔ y) = x.
  Proof.
    intros x y.
    destruct x as [| [x Vx]]; destruct y as [| [y Vy]]; try reflexivity.
    unfold meet. unfold join.
    f_equal.
    apply subset_eq_compat.
    apply merge_Some; try reflexivity.
    intros n.
    cbn.
    rewrite lookup_merge.
    destruct (x !! n) as [xs |] eqn : HX; destruct (y !! n) as [ys |] eqn : HY; try reflexivity.
    2: {
      cbn. rewrite zip_with_bit_meet_idemp. reflexivity.
    }
    unfold valid in Vx, Vy.
    specialize (Vx n).
    rewrite HX in Vx.
    specialize (Vy n).
    rewrite HY in Vy.
    assert (Len : length xs = length ys). {
      rewrite Vx, Vy. reflexivity.
    }
    cbn.
    clear HX HY Vx x Vy y n.
    generalize dependent ys.
    induction xs as [| x xs IH].
    - reflexivity.
    - intros ys Len.
      destruct ys as [| y ys]; cbn in Len; try discriminate.
      cbn [zip_with].
      rewrite option_all_is_alt.
      cbn [option_all_alt].
      rewrite <- option_all_is_alt.
      rewrite <- IH; [ idtac | lia ].
      destruct x, y; reflexivity.
  Qed.

  Lemma join_id : ∀ x, x ⊔ ⊥ = x.
  Proof.
    intros x.
    destruct x as [| [x Vx]]; try reflexivity.
    cbn; f_equal; apply subset_eq_compat.
    apply merge_Some; try reflexivity.
    intros i.
    rewrite lookup_empty.
    cbn; destruct_match; reflexivity.
  Qed.

  Lemma meet_id : ∀ x, x ⊓ ⊤ = x.
  Proof. intros x; destruct x; reflexivity. Qed.

  Definition leb_aux (x y : gmap nat (list ubit)) : bool :=
    forallb (fun '(k, xv) =>
              match y !! k with
              | None    => false
              | Some yv => forallb (fun '(xb, yb) => bit_leb xb yb) (zip xv yv)
              end)
            (map_to_list x).

  Definition leb (x y : t) : bool :=
    match (x, y) with
    | (_, ⊤) => true
    | (⊤, _) => false
    | (Bvs x, Bvs y) => leb_aux (`x) (`y)
    end.

  Lemma forallb_elem_true : ∀ {A} {P} {x : A} {xs}, forallb P xs = true -> x ∈ xs -> P x = true.
  Proof.
    intros A P x xs F E.
    generalize dependent x.
    induction xs as [| x' xs IH].
    - intros. exfalso. rewrite elem_of_nil in E. exact E.
    - intros x E.
      cbn in F.
      rewrite andb_true_iff in F.
      destruct F as [Fhd Ftl].
      apply elem_of_cons in E.
      destruct E as [? | E]; [ subst; exact Fhd | apply (IH Ftl x E) ].
  Qed.

  Lemma leb_join_def_1 : ∀ x y, leb x y = true → y = x ⊔ y.
  Proof.
    intros x y H.
    destruct x as [| [x Vx]]; destruct y as [| [y Vy]]; try (cbn in *; discriminate + reflexivity).
    unfold join; cbn; f_equal; apply subset_eq_compat.
    symmetry.
    apply merge_Some; try reflexivity.
    intros i.
    cbn in H.
    destruct (x !! i) as [xs |] eqn : HX; destruct (y !! i) as [ys |] eqn : HY; try reflexivity.
    all: (
      unfold leb_aux in H;
      rewrite <- elem_of_map_to_list in HX;
      assert (L := forallb_elem_true H HX);
      cbn - [bit_leb] in L;
      rewrite HY in L;
      try discriminate
    ).
    rewrite elem_of_map_to_list in HX.
    unfold valid in Vx, Vy.
    specialize (Vx i).
    rewrite HX in Vx.
    specialize (Vy i).
    rewrite HY in Vy.
    assert (xs_ys_length : length xs = length ys). {
      rewrite Vx, Vy. reflexivity.
    }
    clear HX HY H Vx x Vy y i.
    generalize dependent ys.
    induction xs as [| x xs IH].
    - cbn; intros; f_equal; apply nil_length_inv; lia.
    - intros.
      destruct ys as [| y ys]; try discriminate.
      cbn - [bit_join].
      repeat f_equal.
      + cbn - [bit_leb] in L.
        rewrite andb_true_iff in L.
        destruct L as [L _].
        destruct x, y; cbn in *; reflexivity + discriminate.
      + cbn - [bit_leb] in IH.
        apply Some_inj, IH; cbn [zip forallb] in L.
        * rewrite andb_true_iff in L.
          destruct L as [_ L].
          exact L.
        * cbn in *.
          lia.
  Qed.

  Lemma leb_join_def_2 : ∀ x y, y = x ⊔ y → leb x y = true.
  Proof.
    intros x y H.
    destruct x as [| [x Vx]]; destruct y as [| [y Vy]]; try (discriminate + reflexivity).
    unfold leb, leb_aux.
    unfold join in H.
    inversion H as [J].
    clear H.
    unfold join_aux in J.
    symmetry in J.
    rewrite <- merge_Some in J; try reflexivity.
    apply forallb_forall.
    cbn [proj1_sig].
    intros [i xs] In_xs.
    specialize (J i).
    apply list_elem_of_In in In_xs.
    apply elem_of_map_to_list in In_xs.
    rewrite In_xs in J.
    destruct (y !! i) as [ys |] eqn : HY; try discriminate.
    unfold valid in Vx, Vy.
    specialize (Vx i).
    rewrite In_xs in Vx.
    specialize (Vy i).
    rewrite HY in Vy.
    assert (xs_ys_length : length xs = length ys). {
      rewrite Vx, Vy. reflexivity.
    }
    clear In_xs HY Vx x Vy y i.
    generalize dependent xs.
    induction ys as [| y ys IH].
    - intros; cbn in *.
      apply nil_length_inv in xs_ys_length; subst; reflexivity.
    - intros.
      destruct xs as [| x xs].
      + cbn in *; discriminate.
      + cbn - [bit_leb].
        rewrite andb_true_iff.
        split.
        * cbn in J. inversion J.
          destruct x, y; cbn in *; reflexivity + discriminate.
        * apply IH; [ idtac | cbn in xs_ys_length; lia ].
          cbn - [bit_join] in *.
          inversion J as [[J1 J2]].
          repeat rewrite <- J2.
          reflexivity.
  Qed.

  Lemma leb_join_def : ∀ x y, leb x y = true ↔ y = x ⊔ y.
  Proof.
    intros x y.
    split; intros H.
    - apply (leb_join_def_1 x y H).
    - apply (leb_join_def_2 x y H).
  Qed.

  Lemma singleton_valid : ∀ {xs n}, length xs = n → valid {[n := xs]}.
  Proof.
    intros xs n H.
    unfold valid.
    intros n'.
    destruct (Nat.eqb n n') eqn : E.
    - rewrite Nat.eqb_eq in E; subst.
      rewrite lookup_singleton_eq.
      reflexivity.
    - rewrite Nat.eqb_neq in E.
      rewrite lookup_singleton_ne; reflexivity + assumption.
  Qed.

  Lemma abs_valid : ∀ bv, valid {[length bv := List.map from_bit bv]}.
  Proof.
    intros bv.
    apply singleton_valid.
    apply length_map.
  Qed.

  Definition le (x y : t) : Prop := Is_true (leb x y).

  Infix "⊑" := le (right associativity, at level 70).

  Lemma leb_le : ∀ x y, leb x y = true <-> x ⊑ y.
  Proof.
    intros x y.
    unfold le.
    rewrite Is_true_true.
    reflexivity.
  Qed.

  Lemma le_join_def : ∀ x y, x ⊑ y <-> y = x ⊔ y.
  Proof.
    intros x y.
    unfold le.
    rewrite Is_true_true.
    apply leb_join_def.
  Qed.

  Definition α (bv : list Bit.bit) : t :=
    Bvs ({[length bv := List.map from_bit bv]} ↾ (abs_valid bv)).

  Definition γ (x : t) : Ensembles.Ensemble (list Bit.bit) :=
    match x with
    | ⊤ => Ensembles.Full_set (list Bit.bit)
    | Bvs x => fun bv => Is_true (leb (α bv) (Bvs x))
    end.

  Infix "⊆" := (Ensembles.Included (list Bit.bit)) (right associativity, at level 70).

  Lemma galois : ∀ x y, α x ⊑ y <-> Ensembles.Singleton (list Bit.bit) x ⊆ γ y.
  Proof.
    intros.
    destruct y as [| [y Vy]].
    - split; intros.
      + cbn.
        intros ??.
        apply (Ensembles.Full_intro).
      + reflexivity.
    - split.
      + intros H zs In.
        unfold Ensembles.In in In.
        destruct In.
        unfold Ensembles.In.
        cbn.
        unfold le, α in H.
        cbn in H.
        exact H.
      + intros H.
        specialize (H x).
        unfold le, leb, α.
        cbn.
        apply H.
        unfold Ensembles.In.
        cbn.
        reflexivity.
  Qed.
End AbsBV.

Module Value.
  Definition t := Ast.value.
End Value.

From Stdlib Require Import Program.

Module AbsValue (DZ : DOMAIN BinInt.Z) (Dbv : DOMAIN BitList) (* <: DOMAIN Value *).
  Inductive value : Type :=
    | V_bitvector : Dbv.t -> value
    | V_vector : list value -> value
    | V_list : list value -> value
    | V_int : DZ.t -> value
    | V_real : Qc -> value
    | V_bool : bool -> value
    | V_tuple : list value -> value
    | V_unit : value
    | V_string : string -> value
    | V_ref : Ast.id_aux -> value
    | V_member : gset Ast.id_aux -> value
    | V_ctor : gmap Ast.id_aux (list value) -> value
    | V_record : gmap Ast.id_aux value -> value
    | V_top : value
    | V_bot : value.

  Fixpoint vdepth (v : value) : nat :=
    match v with
    | V_vector vs => fold_right max 0 (map vdepth vs) + 1
    | V_list vs => fold_right max 0 (map vdepth vs) + 1
    | V_tuple vs => fold_right max 0 (map vdepth vs) + 1
    | V_ctor m => map_fold (fun _ vs acc => foldr max acc (map vdepth vs)) 0 m + 1
    | V_record m => map_fold (fun _ v acc => max acc (vdepth v)) 0 m + 1
    | _ => 0
    end.

  Lemma gmap_fmap_tail : ∀ (v : value) (vs : list value) (m : gmap Ast.id_aux (list value)),
    v :: vs ∈ map snd (map_to_list m) -> vs ∈ map snd (map_to_list (tail <$> m)).
  Proof.
    intros v vs m Hin.
    rewrite list_elem_of_fmap in Hin.
    destruct Hin as [[k ws] [Heq Hkin]].
    cbn in Heq. subst ws.
    rewrite elem_of_map_to_list in Hkin.
    rewrite list_elem_of_fmap.
    exists (k, vs).
    split; [reflexivity|].
    rewrite elem_of_map_to_list.
    rewrite lookup_fmap, Hkin.
    reflexivity.
  Qed.

  #[local]
  Lemma foldr_max_mono : ∀ (ds : list nat) (a b : nat),
    a ≤ b → foldr max a ds ≤ foldr max b ds.
  Proof.
    intros ds. induction ds as [| d ds IH].
    - intros a b H. exact H.
    - intros a b H. cbn. apply Nat.max_le_compat_l. apply IH. exact H.
  Qed.

  #[local]
  Lemma foldr_max_ge_init : ∀ (ds : list nat) (init : nat),
    init ≤ foldr max init ds.
  Proof.
    intros ds. induction ds as [| d ds IH].
    - intros. reflexivity.
    - intros init. cbn. specialize (IH init). lia.
  Qed.

  Lemma vdepth_ctor : ∀ (v : value) (vs : list value) (m : gmap Ast.id_aux (list value)),
    v :: vs ∈ map snd (map_to_list m) → vdepth v < vdepth (V_ctor m).
  Proof.
    intros v vs m Hin.
    rewrite list_elem_of_fmap in Hin.
    destruct Hin as [[k ws] [Heq Hkin]].
    cbn in Heq. subst ws.
    rewrite elem_of_map_to_list in Hkin.
    cbn.
    (* Use map_fold_weak_ind to prove: for all k xs, m !! k = Some xs →
       foldr max 0 (map vdepth xs) ≤ map_fold (fun _ xs acc => foldr max acc (map vdepth xs)) 0 m *)
    assert (Hall : ∀ k' xs', m !! k' = Some xs' →
              foldr max 0 (map vdepth xs') ≤
              map_fold (fun (_ : Ast.id_aux) xs acc => foldr max acc (map vdepth xs)) 0 m).
    { apply (map_fold_weak_ind
               (fun r m => ∀ k' xs', m !! k' = Some xs' →
                 foldr max 0 (map vdepth xs') ≤ r)).
      - intros k' xs'. rewrite lookup_empty. discriminate.
      - intros i x m' r Hni IH k' xs' Hlook.
        rewrite lookup_insert_Some in Hlook.
        destruct Hlook as [[Hi Hx] | [Hne Hm']].
        + subst k' xs'.
          apply foldr_max_mono. lia.
        + specialize (IH k' xs' Hm').
          etransitivity; [exact IH|].
          apply foldr_max_ge_init. }
    specialize (Hall k (v :: vs) Hkin).
    cbn in Hall. lia.
  Qed.

  #[local]
  Lemma foldr_max_tail_le : ∀ (xs : list value) (a b : nat),
    a ≤ b → foldr max a (map vdepth (tail xs)) ≤ foldr max b (map vdepth xs).
  Proof.
    intros xs. induction xs as [| x xs' _].
    - intros a b H. cbn. exact H.
    - intros a b H. cbn.
      apply Nat.le_trans with (foldr max b (map vdepth xs')).
      + apply foldr_max_mono. exact H.
      + lia.
  Qed.

  #[local]
  Lemma foldr_max_init : ∀ (ds : list nat) (a : nat),
    foldr max a ds = max a (foldr max 0 ds).
  Proof.
    intros ds. induction ds as [| d ds IH].
    - intros a. cbn. lia.
    - intros a. cbn. rewrite IH. lia.
  Qed.

  #[local]
  Lemma foldr_max_assoc_comm : ∀ (ds1 ds2 : list nat) (y : nat),
    foldr max (foldr max y ds2) ds1 = foldr max (foldr max y ds1) ds2.
  Proof.
    intros ds1 ds2 y.
    rewrite (foldr_max_init ds2 y).
    rewrite (foldr_max_init ds1 y).
    rewrite (foldr_max_init ds1 (max y (foldr max 0 ds2))).
    rewrite (foldr_max_init ds2 (max y (foldr max 0 ds1))).
    set (a := foldr max 0 ds1). set (b := foldr max 0 ds2).
    lia.
  Qed.

  Lemma vdepth_ctor_tail : ∀ m, vdepth (V_ctor (tail <$> m)) <= vdepth (V_ctor m).
  Proof.
    intros m. cbn.
    rewrite map_fold_fmap.
    enough (H : map_fold (fun (_ : Ast.id_aux) (vs : list value) acc => foldr max acc (map vdepth (tail vs))) 0 m ≤
                map_fold (fun (_ : Ast.id_aux) (vs : list value) acc => foldr max acc (map vdepth vs)) 0 m)
      by (apply (Nat.add_le_mono_r _ _ 1) in H; exact H).
    apply (map_fold_weak_ind
             (fun r m =>
                map_fold (fun _ vs acc => foldr max acc (map vdepth (tail vs))) 0 m ≤ r)).
    - rewrite map_fold_empty. reflexivity.
    - intros i x m' r Hni IH.
      rewrite (map_fold_insert_L (fun _ vs acc => foldr max acc (map vdepth (tail vs)))).
      + apply foldr_max_tail_le. exact IH.
      + intros j1 j2 z1 z2 y Hne Hl1 Hl2.
        apply foldr_max_assoc_comm.
      + exact Hni.
  Qed.

  Lemma vdepth_record : ∀ (v : value) (m : gmap Ast.id_aux value),
    v ∈ map snd (map_to_list m) → vdepth v < vdepth (V_record m).
  Proof.
    intros v m Hin.
    rewrite list_elem_of_fmap in Hin.
    destruct Hin as [[k w] [Heq Hkin]].
    cbn in Heq. subst w.
    rewrite elem_of_map_to_list in Hkin.
    cbn.
    assert (Hall : ∀ k' v', m !! k' = Some v' →
              vdepth v' ≤
              map_fold (fun (_ : Ast.id_aux) v acc => max acc (vdepth v)) 0 m).
    { apply (map_fold_weak_ind
               (fun r m => ∀ k' v', m !! k' = Some v' → vdepth v' ≤ r)).
      - intros k' v'. rewrite lookup_empty. discriminate.
      - intros i x m' r Hni IH k' v' Hlook.
        rewrite lookup_insert_Some in Hlook.
        destruct Hlook as [[Hi Hx] | [Hne Hm']].
        + subst k' v'. lia.
        + specialize (IH k' v' Hm'). lia. }
    specialize (Hall k v Hkin).
    lia.
  Qed.

  (* Induction rule for abstract values, needed as they contain nested lists of values,
     as well as gmaps containing values, which is what makes this tricky to define. *)
  Section abs_value_ind.
    Variables (P : value -> Prop)
              (H_bitvector : forall bv, P (V_bitvector bv))
              (H_vector : forall vs, Forall P vs -> P (V_vector vs))
              (H_list : forall vs, Forall P vs -> P (V_list vs))
              (H_int : forall i, P (V_int i))
              (H_real : forall r, P (V_real r))
              (H_bool : forall b, P (V_bool b))
              (H_tuple : forall vs, Forall P vs -> P (V_tuple vs))
              (H_unit : P V_unit)
              (H_string : forall str, P (V_string str))
              (H_ref : forall id, P (V_ref id))
              (H_member : forall (id : gset Ast.id_aux), P (V_member id))
              (H_ctor : ∀ m, (∀ vs, vs ∈ List.map snd (map_to_list m) -> Forall P vs) -> P (V_ctor m))
              (H_record : ∀ fields, (∀ v, v ∈ List.map snd (map_to_list fields) -> P v) -> P (V_record fields))
              (H_top : P V_top)
              (H_bot : P V_bot).

    #[local]
    Obligation Tactic := program_simpl.

    Lemma rec_list : ∀ vs, (∀ v, vdepth v < foldr max 0 (map vdepth vs) + 1 → P v) → Forall P vs.
    Proof using P.
      intros vs H.
      induction vs as [| v vs IH].
      - apply Forall_nil_2.
      - rewrite Forall_cons_iff. split.
        + apply H. cbn. lia.
        + apply IH; intros.
          apply H. cbn. lia.
    Qed.

    Lemma rec_Vector : ∀ vs, (∀ v, vdepth v < vdepth (V_vector vs) → P v) → Forall P vs.
    Proof using P. cbn. apply rec_list. Qed.

    Lemma rec_List : ∀ vs, (∀ v, vdepth v < vdepth (V_list vs) → P v) → Forall P vs.
    Proof using P. cbn. apply rec_list. Qed.

    Lemma rec_Tuple : ∀ vs, (∀ v, vdepth v < vdepth (V_vector vs) → P v) → Forall P vs.
    Proof using P. cbn. apply rec_list. Qed.

    Lemma rec_Ctor : ∀ (m : gmap Ast.id_aux (list value)) vs, (∀ v', vdepth v' < vdepth (V_ctor m) → P v') → vs ∈ List.map snd (map_to_list m) -> Forall P vs.
    Proof using P.
      intros m vs H In.
      generalize dependent m.
      induction vs as [| v vs IH].
      - intros. apply Forall_nil_2.
      - intros m H In.
        rewrite Forall_cons_iff. split.
        + apply H.
          apply (vdepth_ctor _ _ _ In).
        + apply (IH (tail <$> m)).
          * intros ? D.
            apply H.
            apply (Nat.lt_le_trans _ _ _ D (vdepth_ctor_tail m)).
          * apply (gmap_fmap_tail _ _ _ In).
    Qed.

    Lemma rec_Fields : ∀ (m : gmap Ast.id_aux value) v, (∀ v', vdepth v' < vdepth (V_record m) → P v') → v ∈ List.map snd (map_to_list m) -> P v.
    Proof using P.
      intros m v H In.
      apply H.
      apply (vdepth_record _ _ In).
    Qed.

    Program Fixpoint abs_value_ind v {measure (vdepth v)} : P v :=
      match v with
      | V_bitvector bv => H_bitvector bv
      | V_vector vs => H_vector vs (rec_Vector vs abs_value_ind)
      | V_list vs => H_list vs (rec_List vs abs_value_ind)
      | V_int i => H_int i
      | V_real q => H_real q
      | V_bool b => H_bool b
      | V_tuple vs => H_tuple vs (rec_Tuple vs abs_value_ind)
      | V_unit => H_unit
      | V_string s => H_string s
      | V_ref id => H_ref id
      | V_member id => H_member id
      | V_ctor m => H_ctor m (fun vs => rec_Ctor m vs abs_value_ind)
      | V_record fields => H_record fields (fun v => rec_Fields fields v abs_value_ind)
      | V_top => H_top
      | V_bot => H_bot
      end.
  End abs_value_ind.
End AbsValue.
