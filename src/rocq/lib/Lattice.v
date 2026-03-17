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
From Stdlib Require Import Sets.Ensembles.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

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
  Infix "⊔" := join (left associativity, at level 50).
  Infix "⊓" := meet (left associativity, at level 50).

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

  Parameter γ : t -> Ensemble C.t.
  Parameter α : C.t -> t.

  Infix "⊆" := (Included C.t) (right associativity, at level 70).

  Parameter galois : forall (x : C.t) y, α x ⊑ y <-> Singleton C.t x ⊆ γ y.
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

  Definition γ (i : interval) : Ensemble Z :=
    match i with
    | Empty => Empty_set Z
    | Ends e => fun n => low_bound e n /\ high_bound e n
    end.

  Definition α (n : Z) : interval := Ends (exist _ (Some n, Some n) (low_high_refl n)).

  Infix "⊑" := le (right associativity, at level 70).
  Infix "⊆" := (Included Z) (right associativity, at level 70).

  Lemma Singleton_eq : forall x y, Singleton Z x y -> y = x.
  Proof. intros ? ? S; destruct S; reflexivity. Qed.

  Lemma proj1_exist : forall {A} (x : A -> Prop) (y : A) (z : x y), proj1_sig (exist x y z) = y.
  Proof. intros; cbn; reflexivity. Qed.

  Lemma galois : forall (x : Z) (y : interval), α x ⊑ y <-> Singleton Z x ⊆ γ y.
  Proof.
    intros x y.
    split.
    - intros Alpha.
      destruct y as [| e]; try discriminate.
      unfold le, join, α in Alpha.
      inversion Alpha as [H].
      clear Alpha.
      unfold γ, Included, In.
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
      unfold Included, γ in Gamma.
      specialize (Gamma x (In_singleton Z x)).
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

Module Value.
  Definition t := Ast.value.
End Value.

(*
Module AbsValue (DZ : DOMAIN BinInt.Z) <: DOMAIN Value.
  Inductive value : Type :=
    | V_bitvector : list Bit.bit -> value
    | V_vector : list value -> value
    | V_list : list value -> value
    | V_int : DZ.t -> value
    | V_real : Qc -> value
    | V_bool : bool -> value
    | V_tuple : list value -> value
    | V_unit : value
    | V_string : string -> value
    | V_ref : Ast.id -> value
    | V_member : Ast.id -> value
    | V_ctor : Ast.id -> list value -> value
    | V_record : list (Ast.id * value) -> value
    | V_top : value
    | V_bot : value.

  (* Induction rule for abstract values, needed as they contain nested lists of values *)
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
              (H_member : forall id, P (V_member id))
              (H_ctor : forall id vs, Forall P vs -> P (V_ctor id vs))
              (H_record : forall fields, Forall (fun f => P (snd f)) fields -> P (V_record fields))
              (H_top : P V_top)
              (H_bot : P V_bot).

    Fixpoint abs_value_ind v : P v.
      destruct v.
      - apply H_bitvector.
      - apply H_vector.
        induction l.
        + trivial.
        + rewrite Forall_cons_iff. easy.
      - apply H_list.
        induction l.
        + trivial.
        + rewrite Forall_cons_iff. easy.
      - apply H_int.
      - apply H_real.
      - apply H_bool.
      - apply H_tuple.
        induction l.
        + trivial.
        + rewrite Forall_cons_iff. easy.
      - apply H_unit.
      - apply H_string.
      - apply H_ref.
      - apply H_member.
      - apply H_ctor.
        induction l.
        + trivial.
        + rewrite Forall_cons_iff. easy.
      - apply H_record.
        induction l.
        + trivial.
        + rewrite Forall_cons_iff. easy.
      - apply H_top.
      - apply H_bot.
    Qed.
  End abs_value_ind.

  Fixpoint is_bot (v : value) : bool :=
    match v with
    | V_bitvector _ | V_real _ | V_bool _ | V_string _ | V_ref _ | V_member _ => false
    | V_vector vs | V_list vs | V_tuple vs => existsb is_bot vs
    | V_int z => DZ.leb z DZ.bot
    | V_ctor _ vs => existsb is_bot vs
    | V_record flds => existsb (fun '(_, v) => is_bot v) flds
    | V_top | V_unit => false
    | V_bot => true
    end.

  Definition Canon (v : value) : Prop := v = V_bot \/ is_bot v = false.

  Definition t := value.

  Definition top := V_top.
  Definition bot := V_bot.

  Notation "⊤" := V_top.
  Notation "⊥" := V_bot.

  Fixpoint map2 {A B C} (f : A -> B -> C) (xs : list A) (ys : list B) : option (list C) :=
    match xs with
    | [] =>
        match ys with
        | [] => Some []
        | _  => None
        end
    | x :: xs =>
        match ys with
        | []      => None
        | y :: ys =>
            match map2 f xs ys with
            | Some zs => Some (f x y :: zs)
            | None    => None
            end
        end
    end.

  Fixpoint join (v₁ v₂ : value) {struct v₁} : value :=
    match (v₁, v₂) with
    | (V_bitvector bv₁, V_bitvector bv₂) => if list_eqb Bit.bit_eqb bv₁ bv₂ then V_bitvector bv₁ else ⊤
    | (V_vector vs₁, V_vector vs₂) => match map2 join vs₁ vs₂ with Some vsᵣ => V_vector vsᵣ | None => ⊤ end
    | (V_list vs₁, V_list vs₂) => match map2 join vs₁ vs₂ with Some vsᵣ => V_list vsᵣ | None => ⊤ end
    | (V_int i₁, V_int i₂) => V_int (DZ.join i₁ i₂)
    | (V_real r₁, V_real r₂) => if Qeq_bool (this r₁) (this r₂) then V_real r₁ else ⊤
    | (V_bool b₁, V_bool b₂) => if Bool.eqb b₁ b₂ then V_bool b₁ else ⊤
    | (V_tuple vs₁, V_tuple vs₂) => match map2 join vs₁ vs₂ with Some vsᵣ => V_tuple vsᵣ | None => ⊤ end
    | (V_unit, V_unit) => V_unit
    | (V_string s₁, V_string s₂) => if (s₁ =? s₂)%string then V_string s₁ else ⊤
    | (⊥, v) => v
    | (v, ⊥) => v
    | (_, _) => ⊤
    end.

  Fixpoint meet (v₁ v₂ : value) {struct v₁} : value :=
    match (v₁, v₂) with
    | (V_bitvector bv₁, V_bitvector bv₂) => if list_eqb Bit.bit_eqb bv₁ bv₂ then V_bitvector bv₁ else ⊥
    | (V_vector vs₁, V_vector vs₂) => match map2 meet vs₁ vs₂ with Some vsᵣ => V_vector vsᵣ | None => ⊥ end
    | (V_list vs₁, V_list vs₂) => match map2 meet vs₁ vs₂ with Some vsᵣ => V_list vsᵣ | None => ⊥ end
    | (V_int i₁, V_int i₂) => V_int (DZ.meet i₁ i₂)
    | (V_real r₁, V_real r₂) => if Qeq_bool (this r₁) (this r₂) then V_real r₁ else ⊥
    | (V_bool b₁, V_bool b₂) => if Bool.eqb b₁ b₂ then V_bool b₁ else ⊥
    | (V_tuple vs₁, V_tuple vs₂) => match map2 meet vs₁ vs₂ with Some vsᵣ => V_tuple vsᵣ | None => ⊥ end
    | (V_unit, V_unit) => V_unit
    | (V_string s₁, V_string s₂) => if (s₁ =? s₂)%string then V_string s₁ else ⊥
    | (⊤, v) => v
    | (v, ⊤) => v
    | (_, _) => ⊥
    end.

  Lemma eq_comm : forall {A} {x y : A}, x = y <-> y = x.
  Proof.
    split; apply eq_sym.
  Qed.

  Lemma map2_comm : forall {A} {xs ys : list A} {f : A -> A -> A}
      (f_comm : forall {x y : A}, List.In x xs -> List.In y ys -> f x y = f y x),
    map2 f xs ys = map2 f ys xs.
  Proof.
    intros A xs ys f f_comm.
    generalize dependent ys.
    induction xs as [| x xs IH]; destruct ys as [| y ys].
    all: try (intros; reflexivity).
    intros f_comm.
    cbn.
    rewrite f_comm; try apply in_eq.
    rewrite IH.
    + reflexivity.
    + intros x' y' In_xs In_ys.
      apply (f_comm x' y' (in_cons _ _ _ In_xs) (in_cons _ _ _ In_ys)).
  Qed.

  Lemma join_comm : forall x y, join x y = join y x.
  Proof.
    intros x;
    induction x using abs_value_ind;
    intros y; destruct y; cbn [join]; try reflexivity.
    - reintros x y.
      rewrite (list_eqb_comm _ Bit.bit_eqb _ _ (@Bit.bit_eqb_comm)).
      destruct (list_eqb Bit.bit_eqb y x) eqn : Eq; try reflexivity.
      apply list_eqb_eq in Eq.
      + rewrite Eq; reflexivity.
      + intros b1 b2 _; destruct b1, b2; split; intros BitEq; reflexivity + (cbn in BitEq; discriminate).
    - reintros xs IH ys.
      rewrite map2_comm.
      + reflexivity.
      + intros x y In_xs In_ys.
        apply (Forall_in _ _ _ IH In_xs).
    - reintros xs IH ys.
      rewrite map2_comm.
      + reflexivity.
      + intros x y In_xs In_ys.
        apply (Forall_in _ _ _ IH In_xs).
    - f_equal; apply DZ.join_comm.
    - rewrite Qeq_bool_comm.
      destruct (Qeq_bool q r) eqn : Eq; try reflexivity.
      f_equal.
      apply Qc_is_canon.
      apply Qeq_bool_eq.
      rewrite Qeq_bool_comm.
      apply Eq.
    - reintros x y; destruct x, y; reflexivity.
    - reintros xs IH ys.
      rewrite map2_comm.
      + reflexivity.
      + intros x y In_xs In_ys.
        apply (Forall_in _ _ _ IH In_xs).
    - reintros sx sy.
      destruct (sx =? sy)%string eqn : Eq.
      + rewrite String.eqb_eq in Eq; subst.
        rewrite String.eqb_refl; reflexivity.
      + rewrite String.eqb_neq, eq_comm, <- String.eqb_neq in Eq.
        rewrite Eq; reflexivity.
  Qed.

  Lemma join_assoc : forall x y z, join x (join y z) = join (join x y) z.
  Admitted.

  Lemma meet_comm : forall x y, meet x y = meet y x.
  Admitted.

  Lemma meet_assoc : forall x y z, meet x (meet y z) = meet (meet x y) z.
  Admitted.
End AbsValue.
*)
