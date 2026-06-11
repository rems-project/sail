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

From stdpp Require Import base.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import bitvector.tactics.

From Sail Require Import SailBase.
From Sail Require Import Ast.
From Sail Require Import Domain.Lattice.
From Sail Require Import OptionUtil.
From Sail Require Bit.
From Sail Require Import BvUtil.
From Sail Require Import Tactics.

Module Dom <: SAIL_BITS.
  Import Bit.Three.

  Definition valid (m : gmap nat (list ubit)) : Prop :=
    ∀ n, match m !! n with
         | Some xs => length xs = n
         | None    => True
         end.

  Inductive bvset : Set :=
    | Top : bvset
    | Bvs : { m : gmap nat (list ubit) | valid m } → bvset.

  Definition to_bv_list (x : bvset) : option (list (list ubit)) :=
    match x with
    | Top => None
    | Bvs x => Some (List.map snd (map_to_list (`x)))
    end.

  Definition t : Set := bvset.

  Definition top := Top.

  Notation "⊤" := Top.

  Lemma empty_is_valid : valid ∅.
  Proof. unfold valid; intros; rewrite lookup_empty; reflexivity. Qed.

  Definition bot : t := Bvs (∅ ↾ empty_is_valid).

  Notation "⊥" := bot.

  Definition join_aux (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    merge (option_join (zip_with bit_join)) x y.

  Lemma join_aux_preserves_valid : ∀ {x y : gmap nat (list ubit)}, valid x → valid y → valid (join_aux x y).
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

  Lemma meet_aux_preserves_valid : ∀ {x y : gmap nat (list ubit)}, valid x → valid y → valid (meet_aux x y).
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

  Lemma Some_inj : ∀ {A} {x y : A}, Some x = Some y → x = y.
  Proof. intros A x y H; inversion H; subst; reflexivity. Qed.

  Lemma option_all_nil : ∀ {A}, @option_all A [] = Some [].
  Proof. intros; cbn; reflexivity. Qed.

  Lemma option_all_cons_nil : ∀ {A} (x : option A) xs, option_all (x :: xs) = Some [] → False.
  Proof.
    intros A x xs.
    rewrite option_all_is_alt.
    destruct x; cbn.
    - destruct (option_all_alt xs); intros; discriminate.
    - intros; discriminate.
  Qed.

  Lemma option_all_cons_cons : ∀ {A} (x : option A) xs y ys,
    option_all (x :: xs) = Some (y :: ys) → x = Some y ∧ option_all xs = Some ys.
  Proof.
    intros A x xs y ys.
    repeat rewrite option_all_is_alt in *.
    destruct x; cbn.
    - destruct (option_all_alt xs) eqn : H1; intros H2; inversion H2.
      apply conj; reflexivity.
    - intros; discriminate.
  Qed.

  Lemma option_all_cons_none : ∀ {A} (x : option A) xs,
    option_all (x :: xs) = None → x = None ∨ option_all xs = None.
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

  Lemma option_all_cons : ∀ {A} (x y : option A) xs ys,
    x = y → option_all xs = option_all ys → option_all (x :: xs) = option_all (y :: ys).
  Proof.
    intros A x y xs ys H1 H2.
    subst.
    repeat rewrite option_all_is_alt in *.
    cbn [option_all_alt].
    rewrite H2.
    reflexivity.
  Qed.

  Lemma zip_with_bit_meet_idemp : ∀ xs, option_all (zip_with bit_meet xs xs) = Some xs.
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

  Lemma forallb_elem_true : ∀ {A} {P} {x : A} {xs}, forallb P xs = true → x ∈ xs → P x = true.
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

  Definition unknown_bit : bvset := Bvs ({[1 := [BU]]} ↾ singleton_valid (length_cons [] BU)).

  Definition zwbv : bvset := Bvs ({[0 := []]} ↾ singleton_valid (length_nil ubit)).

  Definition le (x y : t) : Prop := Is_true (leb x y).

  Infix "⊑" := le (right associativity, at level 70).

  Lemma leb_le : ∀ x y, leb x y = true ↔ x ⊑ y.
  Proof.
    intros x y.
    unfold le.
    rewrite Is_true_true.
    reflexivity.
  Qed.

  Lemma le_join_def : ∀ x y, x ⊑ y ↔ y = x ⊔ y.
  Proof.
    intros x y.
    unfold le.
    rewrite Is_true_true.
    apply leb_join_def.
  Qed.

  Lemma abs_valid : ∀ {n} (x : bv n), valid {[N.to_nat n := List.map from_bool (bv_to_bits x)]}.
  Proof.
    intros n x.
    apply singleton_valid.
    rewrite length_map.
    apply length_bv_to_bits.
  Qed.

  Definition α (x : bvn) : bvset :=
    let len := bvn_n x in
    match bvn_to_bv len x with
    | Some x' =>
        Bvs ({[N.to_nat len := List.map from_bool (bv_to_bits x')]} ↾ (abs_valid x'))
    | None => ⊥
    end.

  (** ASCII alias for [α], so OCaml code consuming the extracted module can
      use the readable name [alpha] instead of the mangled [_UU03b1_]. *)
  Definition alpha := α.

  Lemma abstract_bvs : ∀ {n} (x : bv n),
     α x = Bvs ({[N.to_nat n := List.map from_bool (bv_to_bits x)]} ↾ abs_valid x).
  Proof.
    intros n x.
    unfold α, bvn_to_bv.
    case_decide.
    - f_equal. apply subset_eq_compat. repeat f_equal.
      rewrite (UIP_refl _ _ H). reflexivity.
    - naive_solver.
  Qed.

  Definition lift_bitwise_gmap (f : ubit → ubit → ubit) (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    intersection_with (λ x y, Some (zip_with f x y)) x y.

  Lemma lift_bitwise_gmap_valid : ∀ f {x y}, valid x → valid y → valid (lift_bitwise_gmap f x y).
  Proof.
    intros f x y Vx Vy n.
    destruct (lift_bitwise_gmap f x y !! n) as [zs |] eqn : H; [| reflexivity].
    unfold lift_bitwise_gmap in H. rewrite lookup_intersection_with_Some in H.
    destruct H as [xs [ys (H1 & H2 & H3)]].
    apply Some_inj in H3.
    unfold valid in Vx, Vy.
    specialize (Vx n). specialize (Vy n).
    rewrite H1 in Vx. rewrite H2 in Vy.
    rewrite <- H3, length_zip_with, Vx, Vy.
    lia.
  Qed.

  Definition lift_bitwise (f : ubit → ubit → ubit) (x y : bvset) : bvset :=
    match (x, y) with
    | (Bvs x, Bvs y) => Bvs (lift_bitwise_gmap f (`x) (`y) ↾ lift_bitwise_gmap_valid f (proj2_sig x) (proj2_sig y))
    | _ => ⊤
    end.

  Definition and (x y : bvset) : bvset := lift_bitwise bit_and x y.

  Definition or (x y : bvset) : bvset := lift_bitwise bit_or x y.

  Definition xor (x y : bvset) : bvset := lift_bitwise bit_xor x y.

  Lemma lift_bitwise_abst : ∀ {bv_op : ∀ n, bv n → bv n → bv n} {bit_op : ubit → ubit → ubit} {bool_op : bool → bool → bool},
    bitwise_op_correct bv_op bit_op bool_op →
    ∀ {n} {x y : bv n}, α (bv_op n x y) = lift_bitwise bit_op (α x) (α y).
  Proof.
    intros ??? Correct n x y.
    repeat rewrite abstract_bvs. unfold lift_bitwise. f_equal.
    apply subset_eq_compat. cbn.
    apply map_eq. intros i. rewrite lookup_intersection_with.
    destruct (decide (i = N.to_nat n)) as [? | H]; [ subst |].
    - repeat rewrite lookup_singleton_eq.
      unfold intersection_with. cbn. f_equal.
      apply Correct.
    - repeat (rewrite lookup_singleton_ne; [| naive_solver]).
      reflexivity.
  Qed.

  Lemma and_abst : ∀ {n} {x y : bv n}, α (bv_and x y) = lift_bitwise bit_and (α x) (α y).
  Proof. intros. apply (lift_bitwise_abst and_correct). Qed.

  Lemma or_abst : ∀ {n} {x y : bv n}, α (bv_or x y) = lift_bitwise bit_or (α x) (α y).
  Proof. intros. apply (lift_bitwise_abst or_correct). Qed.

  Lemma xor_abst : ∀ {n} {x y : bv n}, α (bv_xor x y) = lift_bitwise bit_xor (α x) (α y).
  Proof. intros. apply (lift_bitwise_abst xor_correct). Qed.

  Definition not_gmap (x : gmap nat (list ubit)) : gmap nat (list ubit) := map bit_not <$> x.

  Lemma not_gmap_valid : ∀ {x}, valid x → valid (not_gmap x).
  Proof.
    intros x H i.
    unfold valid, not_gmap in *.
    specialize (H i).
    rewrite lookup_fmap.
    destruct (x !! i) as [x' |]; [| reflexivity].
    cbn. rewrite length_map. apply H.
  Qed.

  Definition not (x : bvset) : bvset :=
    match x with
    | Bvs x => Bvs (not_gmap (`x) ↾ not_gmap_valid (proj2_sig x))
    | _ => ⊤
    end.

  Lemma not_abst : ∀ {n} {x : bv n}, α (bv_not x) = not (α x).
  Proof.
    intros n x.
    unfold not, not_gmap.
    repeat rewrite abstract_bvs. f_equal.
    apply subset_eq_compat. cbn.
    rewrite map_fmap_singleton. f_equal.
    apply (list_eq_same_length _ _ (N.to_nat n)).
    - simp_length.
    - simp_length.
    - intros i b1 b2 i_lt_n L R.
      rewrite list_lookup_map in L. apply option_map_from_bool_Some in L. destruct L as [b3 [L2 L3]].
      rewrite map_map, list_lookup_map in R. apply option_map_from_bool_Some in R. destruct R as [b4 [R2 R3]].
      rewrite bv_to_bits_lookup_Some in L2. destruct L2 as [_ L2].
      rewrite bv_to_bits_lookup_Some in R2. destruct R2 as [_ R2].
      subst. rewrite bit_not_from_bool. bv_simplify.
      rewrite bv_wrap_spec_low, Z.lnot_spec; [ reflexivity | lia | lia ].
  Qed.

  Definition add_gmap (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    intersection_with (λ x y, Some (rev (fst (bitlist_add_carry_acc x y B0 [])))) x y.

  Lemma add_gmap_valid : ∀ {x y}, valid x → valid y → valid (add_gmap x y).
  Proof.
    intros x y Vx Vy i.
    unfold valid in *.
    specialize (Vx i). specialize (Vy i).
    destruct (add_gmap x y !! i) as [zs |] eqn : H; [| reflexivity].
    unfold add_gmap in H. rewrite lookup_intersection_with_Some in H.
    destruct H as [xs [ys (H1 & H2 & H3)]].
    rewrite H1 in Vx.
    rewrite H2 in Vy.
    apply Some_inj in H3.
    rewrite <- H3.
    simp_length.
  Qed.

  Definition add (x y : bvset) : bvset :=
    match (x, y) with
    | (Bvs x, Bvs y) => Bvs (add_gmap (`x) (`y) ↾ add_gmap_valid (proj2_sig x) (proj2_sig y))
    | _ => ⊤
    end.

  Lemma concrete_bitlist_bools : ∀ {xs ys zs n c c'},
    length xs = length ys
    → bitlist_add_carry_acc (map from_bool xs) (map from_bool ys) (from_bool c) (map from_bool zs) = (n, c')
    → ∃ nb cb, n = map from_bool nb ∧ c' = from_bool cb ∧ BoolList.add_carry_acc xs ys c zs = (nb, cb).
  Proof.
    intros xs.
    induction xs as [| x xs IH]; intros ys zs n c c' L H.
    - cbn in *.
      exists zs, c.
      naive_solver.
    - destruct ys as [| y ys]; [ cbn in L; discriminate |].
      cbn [bitlist_add_carry_acc map] in *.
      destruct (bit_add_carry (from_bool x) (from_bool y) (from_bool c)) as (z, c'') eqn : Add.
      assert (A : ∃ a, c'' = from_bool a).
      { exists (to_bool false c''). destruct x, y, z, c, c''; cbn in Add |- *; discriminate + reflexivity. }
      destruct A as [a A].
      assert (Z : ∃ ζ, z = from_bool ζ).
      { exists (to_bool false z). destruct x, y, z, c, c''; cbn in Add |- *; discriminate + reflexivity. }
      destruct Z as [ζ Z].
      rewrite A, Z in H.
      cbn [length] in L. apply eq_add_S in L.
      specialize (IH ys (ζ :: zs) n a c' L H).
      destruct IH as [nb [cb (IH1 & IH2 & IH3)]].
      exists nb, cb.
      cbn [BoolList.add_carry_acc].
      split; [ apply IH1 |].
      split; [ apply IH2 |].
      assert (S : BoolList.bool_add_carry x y c = (ζ, a)).
      { destruct x, y, z, c, c'', a, ζ; cbn in *; discriminate + reflexivity. }
      rewrite S.
      apply IH3.
  Qed.

  Lemma add_abst : ∀ {n} {x y : bv n}, α (x + y)%bv = add (α x) (α y).
  Proof.
    intros n x y.
    repeat rewrite abstract_bvs. unfold add, add_gmap. f_equal.
    apply subset_eq_compat.
    apply map_eq. intros i.
    rewrite lookup_intersection_with. cbn.
    destruct (decide (i = N.to_nat n)) as [? | H]; [ subst |].
    - repeat rewrite lookup_singleton_eq.
      unfold intersection_with. cbn. f_equal.
      apply (list_eq_same_length _ _ (N.to_nat n)).
      + simp_length.
      + simp_length.
      + intros i xb yb i_lt_n L R.
        rewrite list_lookup_map in L. apply option_map_from_bool_Some in L.
        destruct L as [z (L & ?)].
        rewrite bv_to_bits_lookup_Some in L.
        destruct L as [_ L].
        subst.
        pose proof (BoolList.to_bv_ex x).
        destruct H as [xs (xs_len & X)].
        specialize (X xs_len).
        pose proof (BoolList.to_bv_ex y).
        destruct H as [ys (ys_len & Y)].
        specialize (Y ys_len).
        subst.
        repeat rewrite bv_cast_bits in R.
        cbn. bv_simplify. rewrite (bv_cast_unsigned ys_len).
        rewrite bv_wrap_spec_low; [| lia].
        repeat rewrite BoolList.to_bv_unsigned.
        repeat rewrite BoolList.bv_round_trip_alt in R.
        rewrite Nat2N.id in i_lt_n.
        apply Nat2N.inj in ys_len.
        symmetry in ys_len.
        destruct (bitlist_add_carry_acc (map from_bool (rev xs)) (map from_bool (rev ys)) B0 []) as (zs, c) eqn : Add.
        replace B0 with (from_bool false) in Add; [| reflexivity ].
        replace [] with (map from_bool []) in Add; [| reflexivity ].
        apply concrete_bitlist_bools in Add; [| rewrite length_rev, length_rev; apply ys_len ].
        destruct Add as [zsb [cb (? & ? & Add)]].
        subst.
        cbn in R. rewrite <- map_rev, list_lookup_map in R. apply option_map_from_bool_Some in R.
        destruct R as [ybb (R1 & R2)].
        subst.
        replace zsb with (rev (rev zsb)) in R1; [| apply rev_involutive ].
        apply BoolList.to_Z_unsigned_testbit in R1.
        subst. f_equal.
        rewrite <- (Z.mod_pow2_bits_low _ (Z.of_nat (length xs)) _); [| lia ].
        rewrite <- BoolList.add_carry_to_Z; [| exact ys_len ].
        f_equal. f_equal.
        unfold BoolList.add_carry.
        rewrite Add, rev_involutive.
        reflexivity.
    - repeat (rewrite lookup_singleton_ne; [| naive_solver]).
      reflexivity.
  Qed.

  Definition append_insert (bv : list ubit) (o : option (list ubit)) : option (list ubit) :=
    match o with
    | Some bv' => Some (zip_with bit_join bv bv')
    | None => Some bv
    end.

  Definition append_gmap (x y : gmap nat (list ubit)) : gmap nat (list ubit) :=
    map_fold (λ n xbv acc, map_fold (λ m ybv acc, partial_alter (append_insert (ybv ++ xbv)) (n + m) acc) acc y) ∅ x.

  Lemma valid_insert_inv (m : gmap nat (list ubit)) n v :
    m !! n = None → valid (<[n:=v]> m) → valid m.
  Proof.
    intros Hn Hv i.
    unfold valid in Hv. specialize (Hv i).
    destruct (decide (n = i)) as [-> | Hi].
    - rewrite Hn. trivial.
    - rewrite lookup_insert_ne in Hv; [exact Hv | exact Hi].
  Qed.

  Lemma partial_alter_preserves_valid (bv : list ubit) k (acc : gmap nat (list ubit)) :
    length bv = k → valid acc → valid (partial_alter (append_insert bv) k acc).
  Proof.
    intros Hlen Hval i.
    destruct (decide (k = i)) as [-> | Hi].
    - rewrite lookup_partial_alter.
      unfold valid in Hval. specialize (Hval i).
      destruct (acc !! i) as [zs |].
      + case_decide; [| congruence].
        cbn -[length zip_with]. rewrite length_zip_with, Hlen, Hval, Nat.min_id. reflexivity.
      + case_decide; [| congruence]. exact Hlen.
    - rewrite lookup_partial_alter_ne; [| exact Hi]. apply Hval.
  Qed.

  Lemma inner_fold_valid (xbv : list ubit) n (y acc : gmap nat (list ubit)) :
    length xbv = n → valid y → valid acc →
    valid (map_fold (λ m ybv acc', partial_alter (append_insert (ybv ++ xbv)) (n + m) acc') acc y).
  Proof.
    intros Hxlen Vy Vacc.
    enough (H : valid y → valid (map_fold (λ m ybv acc', partial_alter (append_insert (ybv ++ xbv)) (n + m) acc') acc y))
      by exact (H Vy).
    apply (map_fold_weak_ind (λ (acc' : gmap nat (list ubit)) my', valid my' → valid acc')).
    - intros _. exact Vacc.
    - intros m ybv my' acc' Hm IH Hv.
      assert (Hybv : length ybv = m). {
        pose proof (Hv m) as Hv'. rewrite lookup_insert_eq in Hv'. exact Hv'.
      }
      apply partial_alter_preserves_valid.
      + rewrite length_app, Hybv, Hxlen. lia.
      + exact (IH (valid_insert_inv _ _ _ Hm Hv)).
  Qed.

  Lemma append_valid : ∀ {x y}, valid x → valid y → valid (append_gmap x y).
  Proof.
    intros x y Vx Vy.
    unfold append_gmap.
    enough (H : valid x → valid (map_fold (λ n xbv acc, map_fold (λ m ybv acc', partial_alter (append_insert (ybv ++ xbv)) (n + m) acc') acc y) ∅ x))
      by exact (H Vx).
    apply (map_fold_weak_ind (λ (acc : gmap nat (list ubit)) mx, valid mx → valid acc)).
    - intros _. apply empty_is_valid.
    - intros n xbv mx acc Hn IH Hv.
      assert (Hxlen : length xbv = n). {
        pose proof (Hv n) as Hv'. rewrite lookup_insert_eq in Hv'. exact Hv'.
      }
      apply inner_fold_valid; [exact Hxlen | exact Vy |].
      exact (IH (valid_insert_inv _ _ _ Hn Hv)).
  Qed.

  Definition append (x y : bvset) : bvset :=
    match (x, y) with
    | (Bvs x, Bvs y) => Bvs (append_gmap (`x) (`y) ↾ append_valid (proj2_sig x) (proj2_sig y))
    | _ => ⊤
    end.

  Lemma append_abst : ∀ {n m} {x : bv n} {y : bv m},
    α (bv_to_bvn (bv_concat (n + m) x y)) = append (α (bv_to_bvn x)) (α (bv_to_bvn y)).
  Proof.
    intros n m x y.
    repeat rewrite abstract_bvs.
    unfold append. f_equal. apply subset_eq_compat. cbn.
    unfold append_gmap.
    rewrite map_fold_singleton, map_fold_singleton.
    apply map_eq. intros i.
    rewrite lookup_partial_alter, lookup_singleton, lookup_empty.
    rewrite N2Nat.inj_add.
    case_decide.
    - cbn [append_insert]. rewrite bv_concat_app, map_app. reflexivity.
    - rewrite lookup_empty. reflexivity.
  Qed.

  Lemma bv_opp_as_not_add_one : ∀ {n} (x : bv n), bv_opp x = bv_add (bv_not x) (Z_to_bv n 1).
  Proof.
    intros n x. apply bv_eq. bv_simplify.
    pose proof (Z.opp_lnot (bv_unsigned x)).
    f_equal. lia.
  Qed.

  Definition one_bits (n : nat) : list ubit :=
    if n =? 0 then [] else B1 :: replicate (n - 1) B0.

  Lemma one_bits_length : ∀ n, length (one_bits n) = n.
  Proof.
    intros n. unfold one_bits.
    destruct (n =? 0) eqn : H.
    - apply Nat.eqb_eq in H. subst. reflexivity.
    - apply Nat.eqb_neq in H. cbn. rewrite length_replicate. lia.
  Qed.

  Lemma bv_testbit_1 : ∀ (n : N) (i : nat),
    i < N.to_nat n → Z.testbit (bv_unsigned (Z_to_bv n 1)) (Z.of_nat i) = (i =? 0).
  Proof.
    intros n i Hi.
    rewrite Z_to_bv_unsigned, bv_wrap_spec_low; [| lia].
    destruct i; [reflexivity | cbn; reflexivity].
  Qed.

  Lemma one_bits_eq_bv1 : ∀ (n : N), one_bits (N.to_nat n) = map from_bool (bv_to_bits (Z_to_bv n 1)).
  Proof.
    intros n.
    apply (list_eq_same_length _ _ (N.to_nat n)).
    - rewrite length_map, length_bv_to_bits. reflexivity.
    - apply one_bits_length.
    - intros i b1 b2 Hi L R.
      rewrite list_lookup_map in R.
      apply option_map_from_bool_Some in R.
      destruct R as [b (Rb & ->)].
      rewrite bv_to_bits_lookup_Some in Rb.
      destruct Rb as [_ Rb]. subst.
      unfold one_bits in L.
      replace (N.to_nat n =? 0) with false in L.
      2: { symmetry; apply Nat.eqb_neq; lia. }
      rewrite bv_testbit_1; [| exact Hi].
      destruct i.
      + cbn in L. injection L as <-. reflexivity.
      + cbn in L. apply lookup_replicate_1 in L. destruct L as [-> _]. reflexivity.
  Qed.

  Definition negate_gmap (x : gmap nat (list ubit)) : gmap nat (list ubit) :=
    add_gmap (not_gmap x) (fmap (λ bits, one_bits (length bits)) x).

  Lemma negate_gmap_valid : ∀ {x}, valid x → valid (negate_gmap x).
  Proof.
    intros x Hv.
    apply add_gmap_valid.
    - exact (not_gmap_valid Hv).
    - intros i. rewrite lookup_fmap.
      unfold valid in Hv. specialize (Hv i).
      destruct (x !! i) as [bits |]; [| reflexivity].
      cbn. rewrite one_bits_length. exact Hv.
  Qed.

  Definition negate (x : bvset) : bvset :=
    match x with
    | Bvs x => Bvs (negate_gmap (`x) ↾ negate_gmap_valid (proj2_sig x))
    | ⊤ => ⊤
    end.

  Lemma negate_abst : ∀ {n} {x : bv n}, α (bv_to_bvn (bv_opp x)) = negate (α (bv_to_bvn x)).
  Proof.
    intros n x.
    pose proof (bv_opp_as_not_add_one x) as Hopp.
    rewrite Hopp, add_abst, not_abst.
    repeat rewrite abstract_bvs.
    unfold negate, add, not. cbn. f_equal. apply subset_eq_compat. cbn.
    unfold negate_gmap.
    rewrite (map_fmap_singleton (λ bits, one_bits (length bits))).
    rewrite length_map, length_bv_to_bits, one_bits_eq_bv1.
    reflexivity.
  Qed.

  Definition sub (x y : bvset) : bvset := add x (negate y).

  Lemma sub_abst : ∀ {n} {x y : bv n}, α (bv_to_bvn (bv_sub x y)) = sub (α (bv_to_bvn x)) (α (bv_to_bvn y)).
  Proof.
    intros n x y.
    unfold sub.
    rewrite bv_sub_add_opp, add_abst, negate_abst.
    reflexivity.
  Qed.

  Definition slice_bits (bits : list ubit) (s m : nat) : list ubit :=
    take m (drop s bits ++ replicate (m - length (drop s bits)) B0).

  Lemma slice_bits_length : ∀ bits s m, length (slice_bits bits s m) = m.
  Proof. intros. unfold slice_bits. simp_length. Qed.

  Hint Rewrite slice_bits_length : length_db.

  Definition slice_gmap (x : gmap nat (list ubit)) (s m : N) : gmap nat (list ubit) :=
    map_fold (λ _ bits acc,
      partial_alter (append_insert (slice_bits bits (N.to_nat s) (N.to_nat m))) (N.to_nat m) acc
    ) ∅ x.

  Lemma slice_gmap_valid : ∀ {x s m}, valid x → valid (slice_gmap x s m).
  Proof.
    intros x s m.
    unfold slice_gmap.
    apply (map_fold_weak_ind (λ acc mx, valid mx → valid acc)).
    - intros _. apply empty_is_valid.
    - intros n bits mx acc Hn IH Hmx.
      apply partial_alter_preserves_valid.
      + apply slice_bits_length.
      + apply IH. exact (valid_insert_inv _ _ _ Hn Hmx).
  Qed.

  Definition slice (x : bvset) (s m : N) : bvset :=
    match x with
    | Bvs x => Bvs (slice_gmap (`x) s m ↾ slice_gmap_valid (proj2_sig x))
    | ⊤ => Bvs ({[N.to_nat m := replicate (N.to_nat m) BU]} ↾ singleton_valid (length_replicate (N.to_nat m) BU))
    end.

  Lemma slice_bits_eq_bv_extract : ∀ {n} (x : bv n) (s m : N),
    List.map from_bool (bv_to_bits (bv_extract s m x)) =
    slice_bits (List.map from_bool (bv_to_bits x)) (N.to_nat s) (N.to_nat m).
  Proof.
    intros n x s m.
    apply (list_eq_same_length _ _ (N.to_nat m)); try simp_length.
    intros i b1 b2 Hi L R.
    rewrite list_lookup_map in L.
    apply option_map_from_bool_Some in L. destruct L as [bl [L1 L2]]. subst b1.
    rewrite bv_to_bits_lookup_Some in L1. destruct L1 as [_ L1].
    unfold slice_bits in R.
    rewrite lookup_take_lt in R; [| exact Hi].
    set (bits := List.map from_bool (bv_to_bits x)).
    set (s_nat := N.to_nat s).
    set (m_nat := N.to_nat m).
    set (n_nat := N.to_nat n).
    destruct (lt_dec i (n_nat - s_nat)) as [Hi2 | Hi2].
    - assert (Hlen : i < length (drop s_nat bits)).
      { unfold bits. rewrite length_drop, length_map, length_bv_to_bits.
        unfold n_nat, s_nat. lia. }
      rewrite lookup_app_l in R; [| exact Hlen].
      rewrite lookup_drop, list_lookup_map in R.
      apply option_map_from_bool_Some in R. destruct R as [br [R1 R2]]. subst b2.
      rewrite bv_to_bits_lookup_Some in R1. destruct R1 as [_ R1].
      rewrite L1, R1. f_equal.
      rewrite bv_extract_unsigned.
      rewrite bv_wrap_spec_low.
      2: { split; [lia |]. rewrite <- N_nat_Z. apply inj_lt. unfold m_nat in Hi. exact Hi. }
      rewrite Z.shiftr_spec; [| lia].
      unfold s_nat. rewrite Nat2Z.inj_add, N_nat_Z. f_equal. lia.
    - apply not_lt in Hi2.
      assert (Hlen : length (drop s_nat bits) ≤ i).
      { unfold bits. rewrite length_drop, length_map, length_bv_to_bits.
        unfold n_nat, s_nat in Hi2. lia. }
      rewrite lookup_app_r in R; [| exact Hlen].
      rewrite lookup_replicate in R. destruct R as [-> _].
      rewrite L1.
      rewrite bv_extract_unsigned.
      rewrite bv_wrap_spec_low.
      2: { split; [lia |]. rewrite <- N_nat_Z. apply inj_lt. unfold m_nat in Hi. exact Hi. }
      rewrite Z.shiftr_spec; [| lia].
      rewrite bv_unsigned_spec_high; [reflexivity |].
      rewrite <- (N_nat_Z n), <- (N_nat_Z s).
      unfold n_nat, s_nat in *. lia.
  Qed.

  Lemma slice_abst : ∀ {n s m} {x : bv n}, α (bv_extract s m x) = slice (α x) s m.
  Proof.
    intros n s m x.
    repeat rewrite abstract_bvs.
    unfold slice. f_equal. apply subset_eq_compat. cbn.
    unfold slice_gmap. rewrite map_fold_singleton.
    apply map_eq. intros i.
    rewrite lookup_partial_alter, lookup_singleton, lookup_empty.
    case_decide as Hi.
    - subst. cbn [append_insert]. f_equal.
      apply slice_bits_eq_bv_extract.
    - rewrite lookup_empty. reflexivity.
  Qed.
End Dom.
