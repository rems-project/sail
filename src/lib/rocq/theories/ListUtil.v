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
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.

Require Import Ast.
Require Import Tactics.

Import ListNotations.

(* * Utilities for working with lists

   This module provides various useful functions and proofs for
   working with Lists that aren't available in the standard library. *)

(* * take_drop, take, drop

   [take n xs] removes the first [n] elements from the list [xs].
   Relatedly, [drop n xs] removes the first [n] elements from [xs].
   [take_drop] provides a combined version that does both
   simultaneously. *)
Fixpoint take_drop {A : Set} (n : nat) (xs : list A) : list A * list A :=
  match (n, xs) with
  | (0, xs) => ([], xs)
  | (S m, []) => ([], [])
  | (S m, x :: xs) =>
      let '(ys, zs) := take_drop m xs in
      (x :: ys, zs)
  end.

Fixpoint take {A : Set} (n : nat) (xs : list A) : list A :=
  match (n, xs) with
  | (0%nat, xs) => []
  | (S m, []) => []
  | (S m, x :: xs) => x :: take m xs
  end.

Fixpoint drop {A : Set} (n : nat) (xs : list A) : list A :=
  match (n, xs) with
  | (0%nat, xs) => xs
  | (S m, []) => []
  | (S m, _ :: xs) => drop m xs
  end.

Lemma take_drop_all : forall [A : Set] (xs : list A),
    take_drop (length xs) xs = (xs, []).
Proof.
  induction xs.
  - reflexivity.
  - cbn. rewrite IHxs. reflexivity.
Qed.

Lemma take_drop_app : forall [A : Set] (xs ys : list A),
    take_drop (length xs) (xs ++ ys) = (xs, ys).
Proof.
  induction xs.
  - reflexivity.
  - cbn. intros. rewrite IHxs. reflexivity.
Qed.

Lemma take_app_drop_h : forall [A : Set] n (xs ys : list A),
  xs ++ ys = take n xs ++ drop n xs ++ ys.
Proof with reflexivity.
  intros A n.
  induction n; intros xs ys.
  - cbn...
  - destruct xs as [| x xs].
    + cbn...
    + cbn.
      rewrite IHn at 1...
Qed.

Lemma take_app_drop : forall [A : Set] n (xs : list A), xs = take n xs ++ drop n xs.
Proof.
  intros A n xs.
  assert (H := take_app_drop_h n xs []).
  repeat rewrite app_nil_r in H.
  assumption.
Qed.

Lemma take_length : forall [A : Set] n (xs : list A),
  (n <= length xs)%nat -> length (take n xs) = n.
Proof.
  intros A n.
  induction n; intros xs H.
  - cbn. reflexivity.
  - destruct xs as [| x xs].
    + cbn in *.
      assert (C := Nat.nle_succ_0 n).
      contradiction.
    + cbn in *.
      apply eq_S.
      apply (IHn _ (le_S_n _ _ H)).
Qed.

Lemma take_drop_split : forall [A : Set] n (xs : list A),
  take_drop n xs = (take n xs, drop n xs).
Proof with reflexivity.
  intros A n.
  induction n; intro xs.
  - cbn...
  - destruct xs as [| x xs]; cbn; [ idtac | rewrite IHn ]...
Qed.

Lemma drop_drop_add : forall [A] n m (xs : list A), drop m (drop n xs) = drop (n + m) xs.
Proof.
  intros A n m.
  induction n as [| n IH]; intros xs.
  - reflexivity.
  - destruct xs as [|x xs].
    + destruct m; reflexivity.
    + apply IH.
Qed.

(* This theorem about [Forall] and [In] is useful. *)
Lemma Forall_in : forall [A] P (x : A) xs, Forall P xs -> In x xs -> P x.
Proof.
  induction xs.
  - easy.
  - cbn.
    rewrite Forall_cons_iff.
    intros.
    destruct H0.
    + rewrite <- H0. easy.
    + apply (fun Q => IHxs Q H0). easy.
Qed.

Lemma Forall_impl_in: forall [A : Type] [P : A -> Prop] (Q : A -> Prop) [l : list A],
  (forall a : A, In a l -> P a -> Q a) -> Forall P l -> Forall Q l.
Proof.
  intros A P Q l impl FP.
  induction l as [|x xs IH].
  - apply Forall_nil.
  - rewrite Forall_cons_iff in *.
    destruct FP as [Px Pxs].
    split.
    + exact (impl x (in_eq x xs) Px).
    + apply (fun P => IH P Pxs).
      intros x' In_xs Px'.
      exact (impl x' (in_cons _ _ _ In_xs) Px').
Qed.

Lemma forallb_take: forall [A] [n] [xs : list A] [P : A -> bool], forallb P xs = true -> forallb P (take n xs) = true.
Proof.
  intros A n xs P All_xs.
  rewrite (take_app_drop n xs), forallb_app, andb_true_iff in All_xs.
  easy.
Qed.

Lemma forallb_drop: forall [A] [n] [xs : list A] [P : A -> bool], forallb P xs = true -> forallb P (drop n xs) = true.
Proof.
  intros A n xs P All_xs.
  rewrite (take_app_drop n xs), forallb_app, andb_true_iff in All_xs.
  easy.
Qed.

Lemma Forall_take: forall [A] [n] [xs : list A] [P : A -> Prop], Forall P xs -> Forall P (take n xs).
Proof.
  intros A n xs P All_xs.
  rewrite (take_app_drop n xs), Forall_app in All_xs.
  easy.
Qed.

Lemma Forall_drop: forall [A] [n] [xs : list A] [P : A -> Prop], Forall P xs -> Forall P (drop n xs).
Proof.
  intros A n xs P All_xs.
  rewrite (take_app_drop n xs), Forall_app in All_xs.
  easy.
Qed.

Lemma in_app_split : forall [A : Set] (x : A) xs, In x xs -> exists ys zs, xs = ys ++ (x :: zs).
Proof with reflexivity.
  intros A x xs x_in_xs.
  induction xs as [| y ys].
  - cbn in x_in_xs.
    contradiction.
  - apply in_inv in x_in_xs.
    destruct x_in_xs as [y_eq_x | x_in_ys].
    + rewrite y_eq_x.
      exists [].
      exists ys...
    + apply IHys in x_in_ys as H.
      destruct H as [zs].
      destruct H as [ws].
      exists (y :: zs).
      exists ws.
      rewrite H...
Qed.

Lemma app_cons_in : forall [A : Set] (x : A) xs ys zs, xs = ys ++ (x :: zs) -> In x xs.
Proof with tauto.
  intros A x xs.
  induction xs as [| w ws]; intros ys zs H.
  - assert (NH := app_cons_not_nil ys zs x)...
  - destruct ys as [| y ys].
    + rewrite app_nil_l in H.
      injection H; intros _ wx.
      rewrite wx.
      apply in_eq.
    + apply in_cons.
      apply (IHws ys zs).
      rewrite <- app_comm_cons in H.
      injection H...
Qed.

(* * Zipping multiple lists together *)
Fixpoint zip {A} (xs ys : list A) : list (A * A) :=
  match (xs, ys) with
  | (x :: xs, y :: ys) => (x, y) :: zip xs ys
  | ([], _) => []
  | (_, []) => []
  end.

Lemma map_fst_zip : forall [A] (xs ys : list A), length xs = length ys -> map fst (zip xs ys) = xs.
Proof.
  intros A xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs _ (Nat.succ_inj _ _ Same_length)).
  rewrite <- H at 2.
  reflexivity.
Qed.

Lemma map_snd_zip : forall [A] (xs ys : list A), length xs = length ys -> map snd (zip xs ys) = ys.
Proof.
  intros A xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs _ (Nat.succ_inj _ _ Same_length)).
  rewrite <- H at 2.
  reflexivity.
Qed.

Lemma zip_fst_snd : forall [A : Set] (xs ys: list A) zs,
  length xs = length ys ->
  zip xs ys = zs <-> xs = List.map fst zs /\ ys = List.map snd zs.
Proof.
  intros A xs ys zs.
  revert xs ys.
  induction zs as [| z zs]; intros xs ys; destruct xs as [| x xs]; destruct ys as [| y ys]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHzs _ _ (Nat.succ_inj _ _ Same_length)).
  split.
  - intros L.
    injection L; intros L1 L2; rewrite <- L1; rewrite <- L2; cbn.
    rewrite (map_fst_zip _ _ (Nat.succ_inj _ _ Same_length)).
    rewrite (map_snd_zip _ _ (Nat.succ_inj _ _ Same_length)).
    easy.
  - intros L.
    destruct z as (x', y').
    cbn in L.
    destruct L as (L1 & L2).
    injection L1; intros L1_1 L1_2.
    injection L2; intros L2_1 L2_2.
    destruct H as [_ H].
    rewrite (H (conj L1_1 L2_1)), L1_2, L2_2.
    reflexivity.
Qed.

(* * list_eqb

   Compare two lists, returning true if both lists have the same
   length and are pointwise equal according to some predicate. *)
Fixpoint list_eqb {A} (pred : A -> A -> bool) (lhs rhs : list A) : bool :=
  match (lhs, rhs) with
  | ([], []) => true
  | ([], _) => false
  | (_, []) => false
  | (x :: xs, y :: ys) => pred x y && list_eqb pred xs ys
  end.

Lemma list_eqb_eq_right : forall A (pred : A -> A -> bool) lhs rhs,
  (forall x y, In x lhs -> pred x y = true -> x = y) ->
  list_eqb pred lhs rhs = true -> lhs = rhs.
Proof.
  intros A pred lhs rhs H.
  revert rhs.
  induction lhs as [| l_hd l_tl].
  - destruct rhs; easy.
  - destruct rhs as [| r_hd r_tl].
    + easy.
    + cbn.
      rewrite andb_true_iff.
      intro B.
      destruct B as (B1 & B2).
      rewrite (H l_hd r_hd (in_eq l_hd l_tl) B1).
      rewrite (fun P => IHl_tl P r_tl B2).
      reflexivity.
      intros x y In_x_l_tl XY.
      assert (In x (l_hd :: l_tl)) as In_x_l.
      apply in_cons; trivial.
      apply (H _ _ In_x_l XY).
Qed.

Lemma list_eqb_refl: forall A (pred : A -> A -> bool) xs,
  (forall x, In x xs -> pred x x = true) -> list_eqb pred xs xs = true.
Proof.
  intros A pred xs H.
  induction xs as [| x xs].
  - reflexivity.
  - cbn.
    rewrite (H _ (in_eq _ _)).
    rewrite IHxs.
    reflexivity.
    intros ? In_xs.
    apply (H _ (in_cons _ _ _ In_xs)).
Qed.

(* If the predicate is definitional equality (for the elements in the
   list at least), then list_eqb is too. *)
Lemma list_eqb_eq : forall A (pred : A -> A -> bool) lhs rhs,
  (forall x y, In x lhs -> pred x y = true <-> x = y) ->
  list_eqb pred lhs rhs = true <-> lhs = rhs.
Proof.
  intros A pred lhs rhs H.
  split.
  - apply (list_eqb_eq_right A pred lhs rhs (fun x y In => proj1 (H x y In))).
  - intro E.
    rewrite E in *.
    apply list_eqb_refl.
    intros x In_rhs.
    apply (proj2 (H x x In_rhs) eq_refl).
Qed.

Lemma list_eqb_sym: forall A (eq : A -> A -> bool) xs ys,
  (forall x y, eq x y = eq y x) -> list_eqb eq xs ys = true -> list_eqb eq ys xs = true.
Proof.
  intros A eq xs ys eq_sym.
  revert ys.
  induction xs as [| x xs].
  - destruct ys as [| y ys]; trivial.
  - destruct ys as [| y ys].
    + trivial.
    + cbn.
      rewrite andb_true_iff.
      intros H.
      destruct H as (H1 & H2).
      rewrite eq_sym.
      rewrite H1.
      rewrite IHxs.
      * reflexivity.
      * apply H2.
Qed.

Lemma list_eqb_comm: forall A (eq : A -> A -> bool) xs ys,
  (forall x y, eq x y = eq y x) -> list_eqb eq xs ys = list_eqb eq ys xs.
Proof.
  intros A eq xs ys eq_sym.
  apply eq_true_iff_eq.
  split.
  - apply (list_eqb_sym A eq xs ys eq_sym).
  - apply (list_eqb_sym A eq ys xs eq_sym).
Qed.

Lemma list_eqb_comm_in: forall A (eq : A -> A -> bool) xs ys,
  (forall x y, In x xs -> eq x y = eq y x) -> list_eqb eq xs ys = list_eqb eq ys xs.
Proof.
  intros A eq xs ys eq_sym.
  revert ys.
  induction xs as [| x xs].
  - destruct ys as [| y ys]; trivial.
  - destruct ys as [| y ys].
    + trivial.
    + cbn.
      rewrite eq_sym.
      rewrite IHxs.
      reflexivity.
      intros x0 y0 x0_in.
      apply eq_sym.
      cbn.
      apply or_intror.
      trivial.
      cbn.
      apply or_introl.
      easy.
Qed.

Lemma list_eqb_trans_in : forall A (eq : A -> A -> bool) xs ys zs,
  (forall x y z, In y ys -> eq x y = true -> eq y z = true -> eq x z = true) ->
  list_eqb eq xs ys = true ->
  list_eqb eq ys zs = true ->
  list_eqb eq xs zs = true.
Proof.
  intros A eq xs ys zs eq_sym.
  revert xs zs.
  induction ys as [| y ys].
  + intros xs zs.
    destruct zs.
    - trivial.
    - cbn. easy.
  + destruct zs as [| z zs].
    - cbn. easy.
    - destruct xs as [| x xs].
      * cbn. easy.
      * cbn.
        intros XY YZ.
        apply andb_true_iff in XY.
        apply andb_true_iff in YZ.
        destruct XY as (XY1 & XY2).
        destruct YZ as (YZ1 & YZ2).
        assert (eq x z = true) as Eq_xz.
        apply (fun P => eq_sym x y z P XY1 YZ1).
        cbn.
        auto.
        rewrite Eq_xz.
        rewrite (fun P => IHys P xs zs XY2 YZ2).
        reflexivity.
        intros x' y' z' In_y' Eq_xy' Eq_yz'.
        apply (eq_sym x' y' z' (in_cons _ _ _ In_y') Eq_xy' Eq_yz').
Qed.

Lemma list_eqb_trans : forall A (eq : A -> A -> bool) xs ys zs,
  (forall x y z, eq x y = true -> eq y z = true -> eq x z = true) ->
  list_eqb eq xs ys = true ->
  list_eqb eq ys zs = true ->
  list_eqb eq xs zs = true.
Proof.
  intros A eq xs ys zs eq_sym XY YZ.
  apply (fun P => list_eqb_trans_in A eq xs ys zs P XY YZ).
  intros x y z ? ? ?.
  apply (eq_sym _ y _); assumption.
Qed.

Lemma list_eqb_false : forall [A : Set] f (xs ys : list A),
  length xs = length ys -> list_eqb f xs ys = false <-> Exists (fun '(x, y) => f x y = false) (zip xs ys).
Proof.
  intros A f xs.
  induction xs as [| x xs]; intro ys; destruct ys as [| y ys]; try discriminate.
  - cbn. rewrite Exists_nil. easy.
  - intros Same_length.
    cbn.
    rewrite Exists_cons, andb_false_iff.
    apply or_iff_compat_l.
    apply IHxs.
    cbn in Same_length.
    apply (Nat.succ_inj _ _ Same_length).
Qed.

Lemma list_eqb_false_app_r : forall [A : Set] f (xs ys zs : list A),
  list_eqb f (drop (length ys) xs) zs = false -> list_eqb f xs (ys ++ zs) = false.
Proof.
  intros A f xs ys zs.
  revert xs zs.
  induction ys as [| y ys]; intros xs zs; destruct xs as [| x xs]; destruct zs as [| z zs]; try easy.
  all: cbn; rewrite andb_false_iff; intros H; apply or_intror; apply (IHys _ _ H).
Qed.

Lemma list_eqb_app : forall [A : Set] f (xs ys zs ws : list A),
  length xs = length zs ->
  list_eqb f (xs ++ ys) (zs ++ ws) = true ->
  list_eqb f ys ws = true.
Proof.
  intros A f xs ys zs ws.
  revert ys zs ws.
  induction xs as [| x xs]; intros ys zs ws; destruct zs as [| z zs]; try easy.
  cbn.
  intro Same_length.
  assert (H := IHxs ys zs ws (Nat.succ_inj _ _ Same_length)).
  rewrite andb_true_iff.
  tauto.
Qed.

Lemma list_eqb_same_length : forall [A : Set] f (xs ys : list A), list_eqb f xs ys = true -> length xs = length ys.
Proof.
  intros A f xs.
  induction xs as [| x xs]; intros ys; destruct ys as [| y ys]; try easy.
  cbn.
  rewrite andb_true_iff.
  intros.
  apply eq_S.
  apply IHxs.
  tauto.
Qed.

Definition Suffix {A} (xs ys : list A) : Prop := exists n, xs = drop n ys.

Lemma Suffix_refl : forall {A} (xs : list A), Suffix xs xs.
Proof with reflexivity.
  intros A xs.
  unfold Suffix.
  exists 0...
Qed.

Lemma Suffix_nil : forall {A} (xs : list A), Suffix [] xs.
Proof.
  intros A xs.
  unfold Suffix.
  exists (List.length xs).
  induction xs as [| x xs].
  - reflexivity.
  - rewrite length_cons; cbn.
    exact IHxs.
Qed.

Lemma Suffix_drop : forall {A} n (xs : list A), Suffix (drop n xs) xs.
Proof with reflexivity.
  intros A n xs.
  unfold Suffix.
  exists n...
Qed.

Lemma Suffix_forallb: forall [A] [xs ys : list A] [P : A -> bool],
  Suffix xs ys -> forallb P ys = true  -> forallb P xs = true.
Proof.
  intros A xs ys P S All_ys.
  unfold Suffix in S.
  destruct S as [n S].
  rewrite (take_app_drop n ys), forallb_app, andb_true_iff, <- S in All_ys.
  easy.
Qed.

Ltac suffix_solve :=
  lazymatch goal with
  | |- Suffix [] ?xs => exact (Suffix_nil xs)
  | |- Suffix ?xs ?xs => exact (Suffix_refl xs)

  | [ H : take_drop ?n ?xs = (?ys, ?zs) |- Suffix ?zs ?xs ] =>
      rewrite (take_drop_split n xs) in H;
      inversion H; subst; suffix_solve

  | |- Suffix (drop ?n ?xs) ?xs => exact (Suffix_drop n xs)
  end.

Definition consume {A B C} (f : list C -> A -> option B * list C) (acc : option (list B) * list C) (x : A) :=
  match acc with
  | (Some rs, xs) =>
      match f xs x with
      | (Some r, xs) => (Some (r :: rs), xs)
      | (None, xs) => (None, xs)
      end
  | (None, xs) => (None, xs)
  end.

Lemma foldl_consume_none : forall {A B C} (f : list C -> A -> option B * list C) xs ys,
  fold_left (consume f) ys (None, xs) = (None, xs).
Proof.
  intros A B C f xs ys.
  revert xs.
  induction ys as [|y ys].
  - reflexivity.
  - exact IHys.
Qed.

Lemma foldl_consume : forall {A B C} (f : list C -> A -> option B * list C) rs xs ys,
  fold_left (consume f) ys (Some rs, xs) =
  match fold_left (consume f) ys (Some [], xs) with
  | (Some rs', ys') => (Some (rs' ++ rs), ys')
  | (None, ys') => (None, ys')
  end.
Proof.
  intros A B C f rs xs ys.
  revert xs rs.
  induction ys as [| y ys].
  - reflexivity.
  - intros xs rs.
    cbn.
    destruct (f xs y) as [o xs'].
    destruct o as [r |].
    + rewrite IHys.
      rewrite (IHys xs' [r]).
      destruct_match; try rewrite <- app_assoc; reflexivity.
    + rewrite foldl_consume_none.
      reflexivity.
Qed.
