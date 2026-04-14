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

From Sail Require Import Domain.Lattice.
From Sail Require Import OptionUtil.
From Sail Require Bit.
From Sail Require Import Tactics.

Module Bits.
  Definition t := bvn.
End Bits.

Module Dom <: DOMAIN Bits.
  Import Bit.Three.

  Definition valid (m : gmap nat (list ubit)) : Prop :=
    ∀ n, match m !! n with
         | Some xs => length xs = n
         | None    => True
         end.

  Inductive bvset : Set :=
    | Top : bvset
    | Bvs : { m : gmap nat (list ubit) | valid m } → bvset.

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

  Definition α (x : bvn) : t :=
    let len := bvn_n x in
    match bvn_to_bv len x with
    | Some x' =>
        Bvs ({[N.to_nat len := List.map from_bool (bv_to_bits x')]} ↾ (abs_valid x'))
    | None => ⊥
    end.
End Dom.
