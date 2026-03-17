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
From Stdlib Require Import FSets.FMapList.
From Stdlib Require Import FSets.FMapFacts.
From Stdlib Require Import Structures.OrdersAlt.
From Stdlib Require Import Structures.OrdersEx.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From Stdlib Require Import RelationClasses.
From Stdlib Require Import Morphisms.

From Sail Require Import Ast.

Lemma string_ltb_trans : forall (s1 s2 s3 : String.string),
  String.ltb s1 s2 = true -> String.ltb s2 s3 = true -> String.ltb s1 s3 = true.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ];
  induction s3 as [| c3 s3 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.compare c2 c3); case_eq (Ascii.compare c1 c3); try congruence.
  all: unfold Ascii.compare.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  repeat rewrite match_ltb_string.
  intros.
  apply (IHs1 s2); easy.
Qed.

Lemma match_ltb_string (s1 s2 : String.string) : (match String.compare s1 s2 with Lt => true | _ => false end = true) = (String.ltb s1 s2 = true).
Proof.
  reflexivity.
Qed.

Lemma string_ltb_not_eqb : forall s1 s2, String.ltb s1 s2 = true -> String.eqb s1 s2 = false.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.eqb c1 c2).
  all: unfold Ascii.compare.
  all: repeat rewrite Ascii.eqb_eq.
  all: repeat rewrite Ascii.eqb_neq.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  rewrite match_ltb_string.
  intros.
  apply IHs1.
  assumption.
  intros E.
  rewrite E.
  lia.
Qed.

Lemma N_of_ascii_inj : forall c1 c2, Ascii.N_of_ascii c1 = Ascii.N_of_ascii c2 -> c1 = c2.
Proof.
  intros c1 c2 H.
  rewrite <- (Ascii.ascii_N_embedding c1).
  rewrite <- (Ascii.ascii_N_embedding c2).
  rewrite H.
  reflexivity.
Qed.

Lemma N_of_ascii_inj_contra : forall c1 c2, c1 <> c2 -> Ascii.N_of_ascii c1 <> Ascii.N_of_ascii c2.
Proof.
  intros c1 c2 H1 H2.
  apply N_of_ascii_inj in H2.
  tauto.
Qed.

Lemma string_ltb_as_gtb : forall s1 s2, String.ltb s1 s2 = false -> String.eqb s1 s2 = false -> String.ltb s2 s1 = true.
Proof.
  induction s1 as [| c1 s1 ];
  induction s2 as [| c2 s2 ].
  all: unfold String.ltb; cbn; try congruence.
  case_eq (Ascii.compare c1 c2); case_eq (Ascii.eqb c1 c2).
  all: unfold Ascii.compare.
  all: repeat rewrite Ascii.eqb_eq.
  all: repeat rewrite Ascii.eqb_neq.
  all: repeat rewrite BinNat.N.compare_eq_iff.
  all: repeat rewrite BinNat.N.compare_lt_iff.
  all: repeat rewrite BinNat.N.compare_gt_iff.
  all: try lia.
  all: try (intro E; rewrite E; try rewrite BinNat.N.compare_refl; lia).
  intro E. rewrite E.
  try rewrite BinNat.N.compare_refl.
  rewrite match_ltb_string.
  intros.
  apply IHs1; assumption.
  intro C.
  apply N_of_ascii_inj_contra in C.
  congruence.
  intros _ LT.
  rewrite <- BinNat.N.compare_lt_iff in LT.
  rewrite LT.
  reflexivity.
Qed.

Definition unwrap_id (id : Ast.id) : id_aux :=
  match id with
  | Id_aux aux _ => aux
  end.

Module Aux.
  Definition t := id_aux.

  Definition unwrap (id : Ast.id) : id_aux :=
    match id with
    | Id_aux aux _ => aux
    end.

  Definition eqb (id1 id2 : t) : bool :=
    match (id1, id2) with
    | (And_bool, And_bool) => true
    | (Or_bool, Or_bool) => true
    | (Id s1, Id s2) => String.eqb s1 s2
    | (Operator s1, Operator s2) => String.eqb s1 s2
    | _ => false
    end.

  Lemma eqb_eq : forall id1 id2, eqb id1 id2 = true <-> id1 = id2.
  Proof.
    intros id1 id2.
    destruct id1, id2; split; intros H; cbn in *.
    all: try (inversion H + rewrite String.eqb_eq in H; subst); discriminate + reflexivity + apply String.eqb_refl.
  Qed.
End Aux.

Definition id_eqb (id1 : id) (id2 : id) : bool :=
  match (id1, id2) with
  | (Id_aux And_bool _, Id_aux And_bool _) => true
  | (Id_aux Or_bool _, Id_aux Or_bool _) => true
  | (Id_aux (Id s1) _, Id_aux (Id s2) _) => String.eqb s1 s2
  | (Id_aux (Operator s1) _, Id_aux (Operator s2) _) => String.eqb s1 s2
  | _ => false
  end.

Definition id_ltb (id1 : id) (id2 : id) : bool :=
  match (id1, id2) with
  | (Id_aux (Id s1) _, Id_aux (Id s2) _) => String.ltb s1 s2
  | (Id_aux (Operator s1) _, Id_aux (Operator s2) _) => String.ltb s1 s2
  | (Id_aux (Id _) _, Id_aux (Operator _) _) => true
  | (Id_aux (Operator _) _, Id_aux (Id _) _) => false
  | (Id_aux And_bool _, _) => false
  | (_, Id_aux And_bool _) => true
  | (Id_aux Or_bool _, _) => false
  | (_, Id_aux Or_bool _) => true
  end.

Lemma id_eqb_string_is_eq : forall s1 s2 l1 l2, id_eqb (Id_aux (Id s1) l1) (Id_aux (Id s2) l2) = true -> s1 = s2.
Proof.
  intros s1 s2 l1 l2.
  cbn.
  rewrite String.eqb_eq.
  tauto.
Qed.

Lemma id_eqb_refl : forall x, id_eqb x x = true.
Proof.
  destruct x as [aux ?].
  destruct aux; cbn; try trivial; rewrite String.eqb_refl; reflexivity.
Qed.

Lemma id_eqb_comm : forall x y, id_eqb x y = id_eqb y x.
Proof.
  destruct x as [x_aux ?].
  destruct y as [y_aux ?].
  destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
Qed.

Lemma id_eqb_sym : forall x y, id_eqb x y = true -> id_eqb y x = true.
Proof.
  destruct x as [x_aux ?].
  destruct y as [y_aux ?].
  destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
Qed.

Lemma id_eqb_trans : forall x y z, id_eqb x y = true -> id_eqb y z = true -> id_eqb x z = true.
Proof.
  destruct x as [x_aux ?].
  destruct y as [y_aux ?].
  destruct z as [z_aux ?].
  destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
  all: cbn.
  all: try easy.
  all: rewrite String.eqb_eq in *.
  all: congruence.
Qed.

Lemma compare_string_refl : forall s, (s ?= s)%string = Eq.
Proof.
  induction s as [| char s'].
  - reflexivity.
  - cbn.
    rewrite IHs'.
    destruct char as [b0 b1 b2 b3 b4 b5 b6 b7].
    repeat (
      match goal with
      | [ b : bool |- _ ] => destruct b
      end
    ).
    all: reflexivity.
Qed.

Module IdOrdered <: Orders.OrderedType.
  Definition t := Ast.id.

  Definition eq (id1 : id) (id2 : id) : Prop := Is_true (id_eqb id1 id2).

  Definition lt (id1 : id) (id2 : id) : Prop := Is_true (id_ltb id1 id2).

  Lemma eq_refl : forall x, eq x x.
  Proof.
    intros.
    unfold eq.
    apply Is_true_eq_left.
    apply (id_eqb_refl x).
  Qed.

  Lemma eq_sym : forall x y, eq x y -> eq y x.
  Proof.
    intros x y H.
    unfold eq in *.
    apply Is_true_eq_left.
    apply Is_true_eq_true in H.
    apply (id_eqb_sym x y H).
  Qed.

  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof.
    intros x y z H1 H2.
    unfold eq in *.
    apply Is_true_eq_left.
    apply Is_true_eq_true in H1.
    apply Is_true_eq_true in H2.
    apply (id_eqb_trans x y z H1 H2).
  Qed.

  Instance eq_equiv : Equivalence eq.
  Proof.
    split.
    - intro x; apply eq_refl.
    - intros x y H; apply (eq_sym _ _ H).
    - intros x y z H1 H2; apply (eq_trans _ _ _ H1 H2).
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct z as [z_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn.
    all: try easy.
    all: intros A B.
    all: apply Is_true_eq_left.
    all: apply Is_true_eq_true in A.
    all: apply Is_true_eq_true in B.
    all: apply (string_ltb_trans _ y_s _); easy.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: cbn.
    all: try easy.
    all: intros A.
    all: apply Is_true_eq_true in A.
    all: apply string_ltb_not_eqb in A.
    all: apply negb_prop_elim.
    all: cbn.
    all: rewrite A.
    all: reflexivity.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split.
    - intro x; unfold complement.
      destruct x as [x_aux ?].
      destruct x_aux as [| | x_s | x_s]; intros H.
      all: cbn in H; try assumption.
      all: apply Is_true_eq_true in H.
      all: cbn in H; unfold String.ltb in H.
      all: rewrite compare_string_refl in H; congruence.
    - intros x y z H1 H2.
      apply (lt_trans _ _ _ H1 H2).
  Qed.

  Lemma eq_lt_compat_left : forall x y z, eq x y -> lt x z -> lt y z.
  Proof.
    destruct x as [x_aux x_l].
    destruct y as [y_aux y_l].
    destruct z as [z_aux z_l].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn; try easy.
    all: (
      intros H;
      unfold eq in H;
      apply Is_true_eq_true in H;
      apply (id_eqb_string_is_eq x_s y_s x_l y_l) in H;
      rewrite H;
      tauto
    ).
  Qed.

  Lemma eq_lt_compat_right : forall x y z, eq x y -> lt z x -> lt z y.
  Proof.
    destruct x as [x_aux x_l].
    destruct y as [y_aux y_l].
    destruct z as [z_aux z_l].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; destruct z_aux as [| | z_s | z_s].
    all: cbn; try easy.
    all: (
      intros H;
      unfold eq in H;
      apply Is_true_eq_true in H;
      apply (id_eqb_string_is_eq x_s y_s x_l y_l) in H;
      rewrite H;
      tauto
    ).
  Qed.

  Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Proof.
    unfold Proper, respectful.
    intros x y XY w z WZ.
    split.
    - intro XW.
      apply (eq_lt_compat_left x y z XY).
      apply (eq_lt_compat_right w z x WZ XW).
    - intro YZ.
      apply (eq_lt_compat_left y x w (eq_sym _ _ XY)).
      apply (eq_lt_compat_right z w y (eq_sym _ _ WZ) YZ).
  Qed.

  Definition compare (x y : id) : comparison :=
    if id_eqb x y then Eq else if id_ltb x y then Lt else Gt.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros x y.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: try (apply CompLt; reflexivity).
    all: try (apply CompEq; reflexivity).
    all: try (apply CompGt; reflexivity).
    - case_eq (String.eqb x_s y_s); intros Heq; cbn.
      + unfold compare; cbn; rewrite Heq.
        apply CompEq.
        apply Is_true_eq_left.
        cbn.
        assumption.
      + case_eq (String.ltb x_s y_s); intros Hlt.
        * unfold compare; cbn; rewrite Heq, Hlt.
          apply CompLt.
          apply Is_true_eq_left.
          cbn.
          assumption.
        * unfold compare; cbn; rewrite Heq, Hlt.
          apply CompGt.
          apply Is_true_eq_left.
          cbn.
          apply (string_ltb_as_gtb _ _ Hlt Heq).
    - case_eq (String.eqb x_s y_s); intros Heq; cbn.
      + unfold compare; cbn; rewrite Heq.
        apply CompEq.
        apply Is_true_eq_left.
        cbn.
        assumption.
      + case_eq (String.ltb x_s y_s); intros Hlt.
        * unfold compare; cbn; rewrite Heq, Hlt.
          apply CompLt.
          apply Is_true_eq_left.
          cbn.
          assumption.
        * unfold compare; cbn; rewrite Heq, Hlt.
          apply CompGt.
          apply Is_true_eq_left.
          cbn.
          apply (string_ltb_as_gtb _ _ Hlt Heq).
  Defined.

  Lemma eq_dec : forall x y : t, { eq x y } + { ~ (eq x y) }.
  Proof.
    intros x y.
    destruct x as [x_aux ?].
    destruct y as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s].
    all: cbn.
    all: try (apply left; tauto).
    all: try (apply right; tauto).
    - case_eq (String.eqb x_s y_s); intros H.
      + apply left. apply Is_true_eq_left. cbn. assumption.
      + apply right. apply negb_prop_elim, Is_true_eq_left, negb_true_iff. cbn. assumption.
    - case_eq (String.eqb x_s y_s); intros H.
      + apply left. apply Is_true_eq_left. cbn. assumption.
      + apply right. apply negb_prop_elim, Is_true_eq_left, negb_true_iff. cbn. assumption.
  Defined.
End IdOrdered.

Module IdOrderOrig := Backport_OT(IdOrdered).

Module IdMap := FMapList.Make(IdOrderOrig).

Module IdMapP := OrdProperties(IdMap).
