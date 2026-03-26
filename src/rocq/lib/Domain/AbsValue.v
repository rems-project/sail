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

From Stdlib Require Import QArith.
From Stdlib Require Import QArith.Qcanon.
From Stdlib Require Import String.
From Stdlib Require Import Program.

From stdpp Require Import base.
From stdpp Require Import gmap.
From stdpp Require Import list.
From stdpp Require Import mapset.

From Sail Require Import Base.
From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import OptionUtil.
From Sail Require Import Tactics.
From Sail Require Import Domain.Lattice.
From Sail Require Domain.AbsBitvector.
From Sail Require Domain.Interval.
From Sail Require Ast.
From Sail Require PatternMatch.
From Sail Require ValueType.

Import Ltac2.Std.

Module Value.
  Definition t := Ast.value.
End Value.

Module Dom (DZ : DOMAIN BinInt.Z) (Dbv : DOMAIN AbsBitvector.BitList) <: DOMAIN Value.
  Module DZP := DomainProperties BinInt.Z DZ.
  Module DbvP := DomainProperties AbsBitvector.BitList Dbv.

  Inductive value : Type :=
    | V_bitvector : Dbv.t → value
    | V_vector : list value → value
    | V_list : list value → value
    | V_int : DZ.t → value
    | V_real : Qc → value
    | V_bool : bool → value
    | V_tuple : list value → value
    | V_unit : value
    | V_string : string → value
    | V_ref : Ast.id_aux → value
    | V_member : gset Ast.id_aux → value
    | V_ctor : gmap Ast.id_aux (list value) → value
    | V_record : gmap Ast.id_aux value → value
    | V_top : value
    | V_bot : value.

  Definition is_unit (v : value) : bool :=
    match v with
    | V_unit => true
    | _ => false
    end.

  Definition is_true (v : value) : bool :=
    match v with
    | V_bool true => true
    | _ => false
    end.

  Definition is_false (v : value) : bool :=
    match v with
    | V_bool false => true
    | _ => false
    end.

  Definition t := value.

  Definition top := V_top.
  Notation "⊤" := V_top.

  Definition bot : t := V_bot.
  Notation "⊥" := V_bot.

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
    v :: vs ∈ map snd (map_to_list m) → vs ∈ map snd (map_to_list (tail <$> m)).
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

  Lemma vdepth_ctor_tail : ∀ m, vdepth (V_ctor (tail <$> m)) ≤ vdepth (V_ctor m).
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
    Variables (P : value → Prop)
              (H_bitvector : ∀ bv, P (V_bitvector bv))
              (H_vector : ∀ vs, Forall P vs → P (V_vector vs))
              (H_list : ∀ vs, Forall P vs → P (V_list vs))
              (H_int : ∀ i, P (V_int i))
              (H_real : ∀ r, P (V_real r))
              (H_bool : ∀ b, P (V_bool b))
              (H_tuple : ∀ vs, Forall P vs → P (V_tuple vs))
              (H_unit : P V_unit)
              (H_string : ∀ str, P (V_string str))
              (H_ref : ∀ id, P (V_ref id))
              (H_member : ∀ (id : gset Ast.id_aux), P (V_member id))
              (H_ctor : ∀ m, (∀ vs, vs ∈ List.map snd (map_to_list m) → Forall P vs) → P (V_ctor m))
              (H_record : ∀ fields, (∀ v, v ∈ List.map snd (map_to_list fields) → P v) → P (V_record fields))
              (H_top : P V_top)
              (H_bot : P V_bot).

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

    Lemma rec_Ctor : ∀ (m : gmap Ast.id_aux (list value)) vs, (∀ v', vdepth v' < vdepth (V_ctor m) → P v') → vs ∈ List.map snd (map_to_list m) → Forall P vs.
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

    Lemma rec_Fields : ∀ (m : gmap Ast.id_aux value) v, (∀ v', vdepth v' < vdepth (V_record m) → P v') → v ∈ List.map snd (map_to_list m) → P v.
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
    Solve Obligations with program_simpl.
  End abs_value_ind.

  Lemma forallb_false_iff : ∀ {A} P (xs : list A), forallb P xs = false ↔ (∃ x, x ∈ xs ∧ P x = false).
  Proof.
    intros ? P xs.
    induction xs as [| x xs IH].
    - cbn; split; intros H.
      + discriminate.
      + destruct H. destruct H as [H _].
        exfalso.
        apply (elem_of_nil x), H.
    - cbn; split; intros H.
      + rewrite andb_false_iff in H.
        destruct H as [H | H].
        * exists x. split.
          ** apply list_elem_of_here.
          ** exact H.
        * rewrite IH in H.
          destruct H as [x'].
          exists x'.
          split.
          ** apply (list_elem_of_further _ _ _ (proj1 H)).
          ** exact (proj2 H).
      + rewrite andb_false_iff.
        destruct H as [x'].
        destruct H as [H1 H2].
        rewrite elem_of_cons in H1.
        destruct H1 as [H1 | H1].
        * left. rewrite <- H1. exact H2.
        * right.
          rewrite IH.
          exists x'.
          split; [ exact H1 | exact H2 ].
  Qed.

  Definition same_keys {V} (m₁ m₂ : gmap Ast.id_aux V) : bool :=
    forallb (fun '(k, _) => is_some (m₂ !! k)) (map_to_list m₁) &&
    forallb (fun '(k, _) => is_some (m₁ !! k)) (map_to_list m₂).

  Definition same_keys_alt_def {V} (x y : gmap Ast.id_aux V) : Prop :=
    ∀ k, is_some (x !! k) = is_some (y !! k).

  Definition same_keys_false_alt_def {V} (x y : gmap Ast.id_aux V) : Prop :=
    ∃ k, is_some (x !! k) ≠ is_some (y !! k).

  Lemma same_keys_alt : ∀ {V} {x y : gmap Ast.id_aux V}, same_keys x y = true ↔ same_keys_alt_def x y.
  Proof.
    intros ? x y.
    split; intros H; unfold same_keys_alt_def, same_keys in *.
    - rewrite andb_true_iff in H.
      intros k.
      destruct H as [H1 H2].
      destruct (x !! k) as [x' |] eqn : Hx; destruct (y !! k) as [y' |] eqn : Hy; try reflexivity.
      + rewrite forallb_forall in H1.
        rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
        specialize (H1 (k, x') Hx).
        cbn in H1. unfold is_some in H1. rewrite Hy in H1.
        discriminate.
      + rewrite forallb_forall in H2.
        rewrite <- elem_of_map_to_list, list_elem_of_In in Hy.
        specialize (H2 (k, y') Hy).
        cbn in H2. unfold is_some in H2. rewrite Hx in H2.
        discriminate.
    - rewrite andb_true_iff.
      split; rewrite forallb_forall; intros [k v] In;
        rewrite <- list_elem_of_In, elem_of_map_to_list in In; cbn; specialize (H k).
      + rewrite <- H, In. reflexivity.
      + rewrite H, In. reflexivity.
  Qed.

  Lemma same_keys_false_alt : ∀ {V} {x y : gmap Ast.id_aux V}, same_keys x y = false ↔ same_keys_false_alt_def x y.
  Proof.
    intros ? x y.
    destruct (same_keys x y) eqn : E; [ rewrite same_keys_alt in E | idtac ].
    - split; intros H; [ discriminate | idtac ].
      unfold same_keys_alt_def in E.
      unfold same_keys_false_alt_def in H.
      exfalso.
      destruct H as [k H].
      apply H, E.
    - split; try reflexivity; intros _.
      unfold same_keys_false_alt_def.
      unfold same_keys in E.
      rewrite andb_false_iff in E.
      destruct E as [E | E]; rewrite forallb_false_iff in E; destruct E as [[k ?] [E1 E2]]; exists k.
      + destruct (x !! k) as [x' |] eqn : Hx; destruct (x !! k) as [y' |] eqn : Hy; rewrite E2; cbn.
        all: try (intros ?; discriminate).
        rewrite elem_of_map_to_list in E1.
        rewrite Hy in E1.
        discriminate.
      + destruct (x !! k) as [x' |] eqn : Hx; destruct (x !! k) as [y' |] eqn : Hy; rewrite E2; cbn.
        all: try (intros ?; discriminate).
        rewrite elem_of_map_to_list in E1.
        rewrite E1.
        cbn. intros ?. discriminate.
  Qed.

  Lemma same_keys_none : ∀ {V} {m₁ m₂ : gmap Ast.id_aux V} {k}, same_keys m₁ m₂ → m₁ !! k = None → m₂ !! k = None.
  Proof.
    intros V m₁ m₂ k Same H1.
    unfold same_keys in Same.
    rewrite Is_true_true, andb_true_iff in Same.
    destruct Same as [_ K].
    rewrite forallb_forall in K.
    destruct (m₂ !! k) as [v₂ |] eqn : H2; [ exfalso | reflexivity ].
    rewrite <- elem_of_map_to_list, list_elem_of_In in H2.
    specialize (K (k, v₂) H2).
    cbn in K.
    unfold is_some in K.
    rewrite H1 in K.
    discriminate.
  Qed.

  Lemma same_keys_comm : ∀ {V} (m₁ m₂ : gmap Ast.id_aux V), same_keys m₁ m₂ = same_keys m₂ m₁.
  Proof.
    intros V x y.
    unfold same_keys.
    rewrite andb_comm.
    reflexivity.
  Qed.

  Lemma same_keys_trans : ∀ {V} {x y z : gmap Ast.id_aux V},
    same_keys x y = true → same_keys y z = true → same_keys x z = true.
  Proof.
    intros ? x y z same_xy same_yz.
    repeat rewrite same_keys_alt in *.
    unfold same_keys_alt_def in *.
    intros k.
    specialize (same_xy k). specialize (same_yz k).
    apply (eq_trans same_xy same_yz).
  Qed.

  Definition ctor_compat (x y : gmap Ast.id_aux (list value)) : bool :=
    same_keys x y &&
    forallb (fun '(k, vx) => from_option (fun vy => length vx =? length vy) false (y !! k)) (map_to_list x).

  Lemma ctor_compat_same_length : ∀ {x y} k {xs ys},
    ctor_compat x y = true → x !! k = Some xs → y !! k = Some ys → length xs = length ys.
  Proof.
    intros x y k xs ys compat Hx Hy.
    unfold ctor_compat in compat.
    rewrite andb_true_iff in compat.
    destruct compat as [_ compat].
    rewrite forallb_forall in compat.
    rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
    specialize (compat (k, xs) Hx).
    cbn in compat. rewrite Hy in compat.
    cbn in compat.
    rewrite Nat.eqb_eq in compat.
    exact compat.
  Qed.

  Lemma ctor_compat_idemp : ∀ {x}, ctor_compat x x = true.
  Proof.
    intros x.
    unfold ctor_compat. rewrite andb_true_iff.
    split.
    - rewrite same_keys_alt. unfold same_keys_alt_def.
      intros. reflexivity.
    - rewrite forallb_forall.
      intros [k v] In.
      rewrite <- list_elem_of_In, elem_of_map_to_list in In.
      rewrite In.
      cbn.
      rewrite Nat.eqb_eq.
      reflexivity.
  Qed.

  Lemma ctor_compat_same_keys : ∀ x y, ctor_compat x y = true → same_keys x y = true.
  Proof.
    intros x y H.
    unfold ctor_compat in H. rewrite andb_true_iff in H.
    destruct H as [H _].
    exact H.
  Qed.

  Definition same_or {A} `{EqDecb A} (e : t) (v : A → t) (x y : A) : t :=
    if x == y then v x else e.

  Fixpoint join (v₁ v₂ : value) : value :=
    match (v₁, v₂) with
    | (V_bitvector bv₁, V_bitvector bv₂) => V_bitvector (Dbv.join bv₁ bv₂)
    | (V_vector vs₁, V_vector vs₂) => from_option V_vector ⊤ (zip_with_opt join vs₁ vs₂)
    | (V_list vs₁, V_list vs₂) => from_option V_list ⊤ (zip_with_opt join vs₁ vs₂)
    | (V_int i₁, V_int i₂) => V_int (DZ.join i₁ i₂)
    | (V_real q₁, V_real q₂) => same_or ⊤ V_real q₁ q₂
    | (V_bool b₁, V_bool b₂) => same_or ⊤ V_bool b₁ b₂
    | (V_tuple vs₁, V_tuple vs₂) => from_option V_tuple ⊤ (zip_with_opt join vs₁ vs₂)
    | (V_unit, V_unit) => V_unit
    | (V_string s₁, V_string s₂) => same_or ⊤ V_string s₁ s₂
    | (V_ref id₁, V_ref id₂) => same_or ⊤ V_ref id₁ id₂
    | (V_member ids₁, V_member ids₂) => V_member (ids₁ ∪ ids₂)
    | (V_ctor m₁, V_ctor m₂) => if ctor_compat m₁ m₂ then V_ctor (merge (option_join (zip_with join)) m₁ m₂) else ⊤
    | (V_record m₁, V_record m₂) => V_record (merge (option_join join) m₁ m₂)
    | (⊥, _) => v₂
    | (_, ⊥) => v₁
    | _ => ⊤
    end.

  Lemma ctor_compat_comm_h : ∀ (x y : gmap Ast.id_aux (list value)),
      same_keys x y
    → forallb (λ '(k, v₁), from_option (λ v₂ : list value, length v₁ =? length v₂) false (y !! k))
              (map_to_list x)
      = true
    → forallb (λ '(k, v₁), from_option (λ v₂ : list value, length v₁ =? length v₂) false (x !! k))
              (map_to_list y)
      = true.
  Proof.
    intros x y Keys H.
    rewrite forallb_forall in *.
    intros [k vy] In_y.
    destruct (x !! k) as [vx |] eqn : Hx.
    rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
    specialize (H (k, vx) Hx).
    destruct (y !! k) as [vy' |] eqn : Hy; cbn in H; rewrite Hy in H; cbn in *.
    + rewrite <- list_elem_of_In, elem_of_map_to_list in In_y.
      rewrite Nat.eqb_eq in *.
      rewrite H.
      f_equal.
      apply Some_inj.
      rewrite <- In_y, <- Hy.
      reflexivity.
    + discriminate.
    + pose proof (same_keys_none Keys Hx) as Hy.
      rewrite <- list_elem_of_In, elem_of_map_to_list, Hy in In_y.
      discriminate.
  Qed.

  Lemma ctor_compat_comm : ∀ x y, ctor_compat x y = ctor_compat y x.
  Proof.
    intros x y.
    unfold ctor_compat.
    apply eq_true_iff_eq.
    repeat rewrite andb_true_iff.
    split.
    all: (
      intros [Keys H]; split;
      [ rewrite same_keys_comm; assumption
      | rewrite <- Is_true_true in Keys; apply (ctor_compat_comm_h _ _ Keys H) ]
    ).
  Qed.

  Lemma ctor_compat_trans : ∀ {x y z},
    ctor_compat x y = true → ctor_compat y z = true → ctor_compat x z = true.
  Proof.
    intros x y z compat_xy compat_yz.
    unfold ctor_compat. rewrite andb_true_iff.
    split.
    - apply ctor_compat_same_keys in compat_xy, compat_yz.
      apply (same_keys_trans compat_xy compat_yz).
    - rewrite forallb_forall.
      intros [k x'] In.
      unfold ctor_compat in compat_xy.
      rewrite andb_true_iff in compat_xy.
      destruct compat_xy as [_ compat_xy].
      rewrite forallb_forall in compat_xy.
      specialize (compat_xy (k, x') In).
      cbn in compat_xy.
      destruct (y !! k) as [y' |] eqn : Hy; cbn in compat_xy; try discriminate.
      unfold ctor_compat in compat_yz.
      rewrite andb_true_iff in compat_yz.
      destruct compat_yz as [_ compat_yz].
      rewrite forallb_forall in compat_yz.
      rewrite <- elem_of_map_to_list, list_elem_of_In in Hy.
      specialize (compat_yz (k, y') Hy).
      cbn in compat_yz.
      destruct (z !! k) as [z' |] eqn : Hz; cbn in compat_xy; try discriminate.
      cbn in compat_yz.
      cbn.
      rewrite Nat.eqb_eq in *.
      apply (eq_trans compat_xy compat_yz).
  Qed.

  Lemma ctor_compat_false_trans : ∀ {x y z},
    ctor_compat x y = false → ctor_compat y z = true → ctor_compat x z = false.
  Proof.
    intros x y z incompat_xy compat_yz.
    unfold ctor_compat in *. rewrite andb_false_iff in *.
    rewrite andb_true_iff in compat_yz.
    destruct compat_yz as [same_yz compat_yz].
    rewrite forallb_forall in compat_yz.
    destruct incompat_xy as [not_same_xy | incompat_xy].
    - left.
      repeat rewrite same_keys_false_alt in *. unfold same_keys_false_alt_def in *.
      destruct not_same_xy as [k not_same_xy].
      exists k.
      rewrite same_keys_alt in same_yz. unfold same_keys_alt_def in same_yz.
      specialize (same_yz k).
      clear compat_yz.
      destruct (x !! k) eqn : Hx;
      destruct (y !! k) eqn : Hy;
      destruct (z !! k) eqn : Hz;
      cbn in *; (intros ?; discriminate) + assumption.
    - rewrite forallb_false_iff in incompat_xy.
      destruct incompat_xy as [[k x'] [Hx incompat_xy]].
      destruct (y !! k) as [y' |] eqn : Hy.
      + right.
        rewrite <- elem_of_map_to_list, list_elem_of_In in Hy.
        specialize (compat_yz (k, y') Hy).
        cbn in compat_yz.
        rewrite forallb_false_iff.
        exists (k, x').
        split; [ exact Hx | idtac ].
        destruct (z !! k) as [z' |] eqn : Hz; try reflexivity.
        cbn in *.
        rewrite Nat.eqb_neq in *.
        rewrite Nat.eqb_eq in compat_yz.
        intros ?. apply incompat_xy. rewrite compat_yz. assumption.
      + left.
        rewrite same_keys_false_alt. unfold same_keys_false_alt_def.
        rewrite same_keys_alt in same_yz. unfold same_keys_alt_def in same_yz.
        rewrite elem_of_map_to_list in Hx.
        exists k. rewrite Hx. cbn.
        specialize (same_yz k). rewrite Hy in same_yz. cbn in same_yz.
        destruct (z !! k) as [z' |] eqn : Hz; cbn; try (reflexivity + intros ?; discriminate).
  Qed.

  Lemma ctor_compat_merge_right : ∀ {f : value → value → value} {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = true → ctor_compat y z = true →
    ctor_compat x (merge (option_join (zip_with f)) y z) = true .
  Proof.
    intros f x y z compat_xy compat_yz.
    unfold ctor_compat. rewrite andb_true_iff.
    split.
    - apply ctor_compat_same_keys in compat_xy, compat_yz.
      repeat rewrite same_keys_alt in *. unfold same_keys_alt_def in *.
      intros k.
      specialize (compat_xy k). specialize (compat_yz k).
      rewrite compat_xy, lookup_merge.
      destruct (y !! k) as [y' |] eqn : Hy; destruct (z !! k) as [z' |] eqn : Hz; try reflexivity.
      cbn in compat_yz. discriminate.
    - rewrite forallb_forall. intros [k x'] In.
      unfold ctor_compat in compat_xy.
      rewrite andb_true_iff in compat_xy.
      destruct compat_xy as [_ H].
      rewrite forallb_forall in H.
      specialize (H (k, x') In).
      cbn in H.
      destruct (y !! k) as [y' |] eqn : Hy; cbn in H; try discriminate.
      rewrite <- elem_of_map_to_list, list_elem_of_In in Hy.
      unfold ctor_compat in compat_yz.
      rewrite andb_true_iff in compat_yz.
      destruct compat_yz as [_ H'].
      rewrite forallb_forall in H'.
      specialize (H' (k, y') Hy).
      cbn in H'.
      destruct (z !! k) as [z' |] eqn : Hz; cbn in H'; try discriminate.
      destruct (merge (option_join (zip_with f)) y z !! k) eqn : Hyz.
      + cbn. rewrite Nat.eqb_eq in *.
        rewrite lookup_merge in Hyz.
        rewrite <- list_elem_of_In, elem_of_map_to_list in Hy.
        rewrite Hy, Hz in Hyz.
        cbn in Hyz.
        inversion Hyz.
        rewrite length_zip_with_l_eq.
        * exact H.
        * exact H'.
      + cbn. rewrite Nat.eqb_eq in *.
        rewrite lookup_merge in Hyz.
        rewrite <- list_elem_of_In, elem_of_map_to_list in Hy.
        rewrite Hy, Hz in Hyz.
        cbn in Hyz.
        discriminate.
  Qed.

  Lemma ctor_compat_merge_left : ∀ {f : value → value → value} {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = true → ctor_compat y z = true →
    ctor_compat (merge (option_join (zip_with f)) x y) z = true.
  Proof.
    intros f x y z compat_xy compat_yz.
    rewrite ctor_compat_comm.
    apply ctor_compat_merge_right.
    - rewrite ctor_compat_comm.
      apply (ctor_compat_trans compat_xy compat_yz).
    - apply compat_xy.
  Qed.

  Lemma ctor_compat_merge_left_false : ∀ {f : value → value → value} {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = true → ctor_compat y z = false →
    ctor_compat (merge (option_join (zip_with f)) x y) z = false.
  Proof.
    intros f x y z compat_xy incompat_yz.
    rewrite ctor_compat_comm.
    unfold ctor_compat in *. rewrite andb_false_iff in *.
    destruct incompat_yz as [not_same_yz | incompat_yz].
    - left.
      rewrite andb_true_iff in compat_xy. destruct compat_xy as [same_xy _].
      rewrite same_keys_alt in same_xy.
      repeat rewrite same_keys_false_alt in *.
      unfold same_keys_alt_def in same_xy.
      unfold same_keys_false_alt_def in *.
      destruct not_same_yz as [k not_same_yz].
      exists k.
      rewrite lookup_merge.
      specialize (same_xy k).
      destruct (x !! k) as [x' |] eqn : Hx; destruct (y !! k) as [y' |] eqn : Hy; destruct (z !! k) as [z' |] eqn : Hz; cbn.
      all: intros ?; try discriminate.
      all: cbn in not_same_yz; apply not_same_yz; reflexivity.
    - rewrite forallb_false_iff in incompat_yz.
      destruct incompat_yz as [[k y'] [In_y incompat_yz]].
      destruct (z !! k) as [z' |] eqn : Hz.
      + right.
        cbn in incompat_yz.
        rewrite forallb_false_iff.
        exists (k, z').
        split; [ rewrite elem_of_map_to_list; exact Hz | idtac ].
        rewrite lookup_merge.
        rewrite elem_of_map_to_list in In_y.
        rewrite In_y.
        destruct (x !! k) as [x' |] eqn : Hx; cbn.
        * rewrite andb_true_iff in compat_xy.
          destruct compat_xy as [_ compat_xy].
          rewrite forallb_forall in compat_xy.
          rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
          specialize (compat_xy (k, x') Hx).
          cbn in compat_xy.
          rewrite In_y in compat_xy.
          cbn in compat_xy.
          rewrite Nat.eqb_neq in *.
          rewrite length_zip_with_r_eq.
          ** symmetry. exact incompat_yz.
          ** rewrite Nat.eqb_eq in compat_xy. symmetry. exact compat_xy.
        * rewrite Nat.eqb_neq in *.
          symmetry.
          exact incompat_yz.
      + left.
        rewrite same_keys_false_alt.
        unfold same_keys_false_alt_def.
        exists k.
        rewrite Hz.
        rewrite lookup_merge.
        rewrite elem_of_map_to_list in In_y.
        rewrite In_y.
        destruct (x !! k) as [x' |] eqn : Hx; cbn; intros ?; discriminate.
  Qed.

  Lemma ctor_compat_merge_right_false : ∀ {f : value → value → value} {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = false → ctor_compat y z = true →
    ctor_compat x (merge (option_join (zip_with f)) y z) = false.
  Proof.
    intros f x y z incompat_xy compat_yz.
    rewrite ctor_compat_comm.
    apply (ctor_compat_merge_left_false compat_yz).
    rewrite ctor_compat_comm.
    apply (ctor_compat_false_trans incompat_xy compat_yz).
  Qed.

  Lemma if_then_simp : ∀ {A} {P : bool} {x y e : A}, (P = true → x = y) → (if P then x else e) = (if P then y else e).
  Proof. intros ? P ??? H. destruct P; [ rewrite H; reflexivity | reflexivity ]. Qed.

  Ltac2 join_if_simp () :=
    lazy_match! goal with
    | [ |- (if ?x then _ else ?_b) = (if ?y then _ else ?_b) ] =>
        let e := Fresh.in_goal (Option.get (Ident.of_string "L")) in
        let rw () :=
          let e_hyp := Control.hyp e in
          rewrite $e_hyp at 1;
          clear $e
        in
        assert ($e : $x = $y) > [ () | rw (); apply if_then_simp ]
    end.

  Ltac join_if_simp := ltac2:(join_if_simp ()).

  Lemma elem_snd : ∀ {K V} (k : K) {v : V} {l}, (k, v) ∈ l → v ∈ map snd l.
  Proof.
    intros ?? k v l H.
    induction l as [| e l IH].
    - exfalso. apply elem_of_nil in H. exact H.
    - cbn.
      repeat rewrite elem_of_cons in *.
      destruct H.
      + left. subst. reflexivity.
      + right. apply IH. exact H.
  Qed.

  Lemma same_or_refl : ∀ {A} `{EqDecb A} {e} {v : A → t} {x},
    same_or e v x x = v x.
  Proof.
    intros ?? e v x.
    unfold same_or.
    rewrite eqb_refl. reflexivity.
  Qed.

  Lemma same_or_comm : ∀ {A} `{EqDecb A} {e} {v : A → t} {x y},
    same_or e v x y = same_or e v y x.
  Proof.
    intros ?? e v x y.
    unfold same_or.
    destruct (x == y) eqn : XY; destruct (y == x) eqn : YX; eqb_to_eq; simplify_eq; reflexivity.
  Qed.

  Lemma join_comm : ∀ x y, join x y = join y x.
  Proof.
    intros x.
    induction x using abs_value_ind; intros y; destruct y; try reflexivity.
    all: try (apply same_or_comm).
    all: try (
      reintros xs IH ys;
      cbn; f_equal;
      apply zip_with_opt_comm; intros x y In_x In_y;
      rewrite Forall_forall in IH;
      apply (IH _ In_x)
    ).
    - cbn; f_equal; apply Dbv.join_comm.
    - cbn; f_equal; apply DZ.join_comm.
    - reintros x y.
      cbn. f_equal.
      set_solver.
    - reintros x IH y.
      cbn.
      join_if_simp.
      + apply ctor_compat_comm.
      + intros Compat. f_equal.
        apply merge_comm.
        intros id.
        destruct (x !! id) as [xs |] eqn : XH;
        destruct (y !! id) as [ys |]; try reflexivity.
        specialize (IH xs).
        assert (L : xs ∈ map snd (map_to_list x)).
        { apply (elem_snd id), elem_of_map_to_list, XH. }
        specialize (IH L).
        cbn. f_equal.
        apply zip_with_comm. intros ?? In_xs ?.
        rewrite Forall_forall in IH.
        apply (IH _ In_xs).
    - reintros xfields IH yfields.
      cbn. f_equal.
      apply merge_comm.
      intros id.
      destruct (xfields !! id) as [x |] eqn : XH;
      destruct (yfields !! id) as [y |]; try reflexivity.
      specialize (IH x).
      cbn. f_equal.
      apply IH.
      apply (elem_snd id), elem_of_map_to_list, XH.
  Qed.

  Ltac2 destruct_from_option () :=
    lazy_match! goal with
    | [ |- context [ from_option _ _ ?opt ] ] =>
        destruct $opt
    end.

  Ltac2 simplify_same_or () :=
    let rec go () :=
      cbn - [eqb];
      match Control.case (fun () => orelse (fun () => Std.discriminate false None) (fun _ => reflexivity ())) with
      | Val ((), _) => ()
      | Err _ =>
          lazy_match! goal with
          | [ h : context [ same_or _ _ ?x ?y ] |- _ ]=>
              let e := Fresh.in_goal (Option.get (Ident.of_string "S")) in
              let rw () :=
              let e_hyp := Control.hyp e in
                unfold same_or in $h at 1;
                rewrite $e_hyp in $h at 1
              in
              destruct ($x == $y) eqn : $e;
              Control.enter (fun () => rw (); go ())
          | [ |- context [ same_or _ _ ?x ?y ] ] =>
              let e := Fresh.in_goal (Option.get (Ident.of_string "S")) in
              let rw () :=
              let e_hyp := Control.hyp e in
                unfold same_or at 1;
                rewrite $e_hyp at 1
              in
              destruct ($x == $y) eqn : $e;
              Control.enter (fun () => rw (); go ())
          | [ |- _ ] => eqb_to_eq ()
          end
      end
    in
    go ().

  Ltac simplify_same_or := ltac2:(Control.enter simplify_same_or).

  Lemma join_assoc : ∀ x y z, join x (join y z) = join (join x y) z.
  Proof.
    intros x y.
    revert x.
    induction y using abs_value_ind; intros x z; destruct x, z; try reflexivity.
    all: try (cbn; ltac2:(Control.enter destruct_from_option); reflexivity).
    all: try (cbn - [Aux.eqb]; unfold same_or; destruct_match_goal; intros; discriminate).
    - cbn. f_equal. apply Dbv.join_assoc.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt join xs ys) as [xys |] eqn : XY; destruct (zip_with_opt join ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt join xs ys) as [xys |] eqn : XY; destruct (zip_with_opt join ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - cbn. f_equal. apply DZ.join_assoc.
    - simplify_same_or; simplify_eq.
    - simplify_same_or; simplify_eq.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt join xs ys) as [xys |] eqn : XY; destruct (zip_with_opt join ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff join) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff join) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - simplify_same_or; simplify_eq.
    - simplify_same_or; simplify_eq.
    - reintros y x z.
      destruct x, y, z.
      cbn. f_equal.
      unfold union, gset_union, mapset_union.
      f_equal.
      apply map_union_assoc.
    - reintros y IH x z.
      cbn.
      destruct (ctor_compat x y) eqn : compat_xy; destruct (ctor_compat y z) eqn : compat_yz.
      + cbn.
        assert (compat_left : ctor_compat x (merge (option_join (zip_with join)) y z) = true).
        { apply (ctor_compat_merge_right compat_xy compat_yz). }
        assert (compat_right : ctor_compat (merge (option_join (zip_with join)) x y) z = true).
        { apply (ctor_compat_merge_left compat_xy compat_yz). }
        rewrite compat_left, compat_right.
        f_equal.
        apply merge_assoc.
        intros i.
        destruct (x !! i) as [xs |]; destruct (y !! i) as [ys |] eqn : HY; destruct (z !! i) as [zs |]; try reflexivity.
        cbn. f_equal.
        apply zip_with_assoc.
        intros x' y' z' elem_xs elem_ys elem_zs.
        specialize (IH ys).
        rewrite Forall_forall in IH.
        apply (fun P => IH P y' elem_ys).
        apply (elem_snd i), elem_of_map_to_list, HY.
      + cbn. rewrite (ctor_compat_merge_left_false compat_xy compat_yz). reflexivity.
      + cbn. rewrite (ctor_compat_merge_right_false compat_xy compat_yz). reflexivity.
      + reflexivity.
    - reintros yfields IH xfields zfields.
      cbn. f_equal.
      apply merge_assoc.
      intros i.
      destruct (xfields !! i) as [x |] eqn : Hx;
      destruct (yfields !! i) as [y |] eqn : Hy;
      destruct (zfields !! i) as [z |] eqn : Hz;
      try reflexivity.
      cbn. f_equal.
      apply IH.
      apply (elem_snd i).
      rewrite elem_of_map_to_list.
      exact Hy.
  Qed.

  Lemma join_idemp : ∀ x, join x x = x.
  Proof.
    intros x.
    induction x using abs_value_ind.
    all: cbn; try reflexivity.
    all: try (apply same_or_refl).
    all: try rewrite (fun zs => from_zip_with_opt (@eq_refl _ (length zs))).
    all: try (rewrite zip_with_idemp; [ reflexivity | rewrite Forall_forall in *; assumption ]).
    - f_equal; apply DbvP.join_idem.
    - f_equal; apply DZP.join_idem.
    - f_equal.
      apply subseteq_union_1_L.
      reflexivity.
    - reintros x IH.
      rewrite ctor_compat_idemp.
      f_equal.
      apply merge_idemp.
      intros i.
      destruct (x !! i) as [xs |] eqn : Hx; cbn; try reflexivity.
      f_equal.
      apply zip_with_idemp.
      rewrite <- elem_of_map_to_list in Hx. apply elem_snd in Hx.
      specialize (IH xs Hx).
      rewrite Forall_forall in IH.
      apply IH.
    - reintros fields IH.
      f_equal.
      apply merge_idemp.
      intros i.
      destruct (fields !! i) as [fld |] eqn : Hfields; cbn; try reflexivity.
      f_equal.
      apply IH, (elem_snd i), elem_of_map_to_list, Hfields.
  Qed.

  Lemma join_id : ∀ x, join x ⊥ = x.
  Proof. intros x. destruct x; reflexivity. Qed.

  Fixpoint meet (v₁ v₂ : value) : value :=
    match (v₁, v₂) with
    | (V_bitvector bv₁, V_bitvector bv₂) => V_bitvector (Dbv.meet bv₁ bv₂)
    | (V_vector vs₁, V_vector vs₂) => from_option V_vector ⊥ (zip_with_opt meet vs₁ vs₂)
    | (V_list vs₁, V_list vs₂) => from_option V_list ⊥ (zip_with_opt meet vs₁ vs₂)
    | (V_int i₁, V_int i₂) => V_int (DZ.meet i₁ i₂)
    | (V_real q₁, V_real q₂) => same_or ⊥ V_real q₁ q₂
    | (V_bool b₁, V_bool b₂) => same_or ⊥ V_bool b₁ b₂
    | (V_tuple vs₁, V_tuple vs₂) => from_option V_tuple ⊥ (zip_with_opt meet vs₁ vs₂)
    | (V_unit, V_unit) => V_unit
    | (V_string s₁, V_string s₂) => same_or ⊥ V_string s₁ s₂
    | (V_ref id₁, V_ref id₂) => same_or ⊥ V_ref id₁ id₂
    | (V_member ids₁, V_member ids₂) => V_member (ids₁ ∩ ids₂)
    | (V_ctor m₁, V_ctor m₂) => if ctor_compat m₁ m₂ then V_ctor (merge (option_join (zip_with meet)) m₁ m₂) else ⊥
    | (V_record m₁, V_record m₂) => V_record (merge (option_map2 meet) m₁ m₂)
    | (⊤, _) => v₂
    | (_, ⊤) => v₁
    | _ => ⊥
    end.

  Lemma meet_idemp : ∀ x, meet x x = x.
  Proof.
    intros x.
    induction x using abs_value_ind.
    all: cbn; try reflexivity.
    all: try (apply same_or_refl).
    all: try rewrite (fun zs => from_zip_with_opt (@eq_refl _ (length zs))).
    all: try (rewrite zip_with_idemp; [ reflexivity | rewrite Forall_forall in *; assumption ]).
    - f_equal; apply DbvP.meet_idem.
    - f_equal; apply DZP.meet_idem.
    - f_equal. set_solver.
    - reintros x IH.
      rewrite ctor_compat_idemp.
      f_equal.
      apply merge_idemp.
      intros i.
      destruct (x !! i) as [xs |] eqn : Hx; cbn; try reflexivity.
      f_equal.
      apply zip_with_idemp.
      rewrite <- elem_of_map_to_list in Hx. apply elem_snd in Hx.
      specialize (IH xs Hx).
      rewrite Forall_forall in IH.
      apply IH.
    - reintros fields IH.
      f_equal.
      apply merge_idemp.
      intros i.
      destruct (fields !! i) as [fld |] eqn : Hfields; cbn; try reflexivity.
      f_equal.
      apply IH, (elem_snd i), elem_of_map_to_list, Hfields.
  Qed.

  Lemma meet_comm : ∀ x y, meet x y = meet y x.
  Proof.
    intros x.
    induction x using abs_value_ind; intros y; destruct y; try reflexivity.
    all: try (apply same_or_comm).
    all: try (
      reintros xs IH ys;
      cbn; f_equal;
      apply zip_with_opt_comm; intros x y In_x In_y;
      rewrite Forall_forall in IH;
      apply (IH _ In_x)
    ).
    - cbn; f_equal; apply Dbv.meet_comm.
    - cbn; f_equal; apply DZ.meet_comm.
    - reintros x y.
      cbn. f_equal.
      set_solver.
    - reintros x IH y.
      cbn.
      join_if_simp.
      + apply ctor_compat_comm.
      + intros Compat. f_equal.
        apply merge_comm.
        intros id.
        destruct (x !! id) as [xs |] eqn : XH;
        destruct (y !! id) as [ys |]; try reflexivity.
        specialize (IH xs).
        assert (L : xs ∈ map snd (map_to_list x)).
        { apply (elem_snd id), elem_of_map_to_list, XH. }
        specialize (IH L).
        cbn. f_equal.
        apply zip_with_comm. intros ?? In_xs ?.
        rewrite Forall_forall in IH.
        apply (IH _ In_xs).
    - reintros xfields IH yfields.
      cbn. f_equal.
      apply merge_comm.
      intros id.
      destruct (xfields !! id) as [x |] eqn : XH;
      destruct (yfields !! id) as [y |]; try reflexivity.
      specialize (IH x).
      cbn. f_equal.
      apply IH.
      apply (elem_snd id), elem_of_map_to_list, XH.
  Qed.

  Lemma meet_assoc : ∀ x y z, meet x (meet y z) = meet (meet x y) z.
  Proof.
    intros x y.
    revert x.
    induction y using abs_value_ind; intros x z; destruct x, z; try reflexivity.
    all: try (cbn; ltac2:(Control.enter destruct_from_option); reflexivity).
    all: try (cbn - [Aux.eqb]; unfold same_or; destruct_match_goal; intros; discriminate).
    - cbn. f_equal. apply Dbv.meet_assoc.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt meet xs ys) as [xys |] eqn : XY; destruct (zip_with_opt meet ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt meet xs ys) as [xys |] eqn : XY; destruct (zip_with_opt meet ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - cbn. f_equal. apply DZ.meet_assoc.
    - simplify_same_or; simplify_eq.
    - simplify_same_or; simplify_eq.
    - reintros ys IH xs zs.
      cbn.
      destruct (zip_with_opt meet xs ys) as [xys |] eqn : XY; destruct (zip_with_opt meet ys zs) as [yzs |] eqn : YZ; cbn.
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L4 [L5 L6]].
        rewrite (from_zip_with_opt (eq_trans L1 L5)).
        rewrite (from_zip_with_opt (eq_trans (eq_sym L3) L4)).
        f_equal.
        apply zip_with_opt_to_zip_with in XY, YZ.
        rewrite <- XY, <- YZ.
        apply zip_with_assoc.
        intros x y z elem_xs elem_ys elem_zs.
        rewrite Forall_forall in IH.
        apply (IH _ elem_ys).
      + pose proof (zip_with_opt_some_length XY) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in YZ.
        assert (L : length xys ≠ length zs).
        { rewrite <- L3. exact YZ. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + pose proof (zip_with_opt_some_length YZ) as L. destruct L as [L1 [L2 L3]].
        rewrite (zip_with_opt_none_iff meet) in XY.
        assert (L : length xs ≠ length yzs).
        { rewrite <- L2. exact XY. }
        rewrite <- (zip_with_opt_none_iff meet) in L.
        rewrite L.
        reflexivity.
      + reflexivity.
    - simplify_same_or; simplify_eq.
    - simplify_same_or; simplify_eq.
    - reintros y x z.
      cbn. f_equal.
      set_solver.
    - reintros y IH x z.
      cbn.
      destruct (ctor_compat x y) eqn : compat_xy; destruct (ctor_compat y z) eqn : compat_yz.
      + cbn.
        assert (compat_left : ctor_compat x (merge (option_join (zip_with meet)) y z) = true).
        { apply (ctor_compat_merge_right compat_xy compat_yz). }
        assert (compat_right : ctor_compat (merge (option_join (zip_with meet)) x y) z = true).
        { apply (ctor_compat_merge_left compat_xy compat_yz). }
        rewrite compat_left, compat_right.
        f_equal.
        apply merge_assoc.
        intros i.
        destruct (x !! i) as [xs |]; destruct (y !! i) as [ys |] eqn : HY; destruct (z !! i) as [zs |]; try reflexivity.
        cbn. f_equal.
        apply zip_with_assoc.
        intros x' y' z' elem_xs elem_ys elem_zs.
        specialize (IH ys).
        rewrite Forall_forall in IH.
        apply (fun P => IH P y' elem_ys).
        apply (elem_snd i), elem_of_map_to_list, HY.
      + cbn. rewrite (ctor_compat_merge_left_false compat_xy compat_yz). reflexivity.
      + cbn. rewrite (ctor_compat_merge_right_false compat_xy compat_yz). reflexivity.
      + reflexivity.
    - reintros yfields IH xfields zfields.
      cbn. f_equal.
      apply merge_assoc.
      intros i.
      destruct (xfields !! i) as [x |] eqn : Hx;
      destruct (yfields !! i) as [y |] eqn : Hy;
      destruct (zfields !! i) as [z |] eqn : Hz;
      try reflexivity.
      cbn. f_equal.
      apply IH.
      apply (elem_snd i).
      rewrite elem_of_map_to_list.
      exact Hy.
  Qed.

  Lemma meet_id : ∀ x, meet x ⊤ = x.
  Proof. intros x. destruct x; reflexivity. Qed.

  Lemma absorption_join_meet : ∀ x y, join x (meet x y) = x.
  Proof.
    intros x.
    induction x using abs_value_ind; intros y; destruct y; try reflexivity.
    all: try (cbn [meet]; rewrite join_idemp; reflexivity).
    all: try solve [ simplify_same_or; simplify_eq ].
    - cbn. rewrite Dbv.absorption_join_meet. reflexivity.
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt meet xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt meet xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - cbn. rewrite DZ.absorption_join_meet. reflexivity.
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt meet xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - reintros x y.
      cbn.
      f_equal.
      set_solver.
    - reintros x IH y.
      cbn.
      destruct (ctor_compat x y) eqn : compat; try reflexivity.
      rewrite (ctor_compat_merge_right ctor_compat_idemp compat).
      f_equal.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite lookup_merge.
      symmetry.
      destruct (x !! i) as [xs |] eqn : Hx; destruct (y !! i) as [ys |] eqn : Hy; cbn.
      + f_equal.
        assert (L : length xs = length ys).
        { unfold ctor_compat in compat.
          rewrite andb_true_iff in compat.
          destruct compat as [_ compat].
          rewrite forallb_forall in compat.
          rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
          specialize (compat (i, xs) Hx).
          cbn in compat.
          rewrite Hy in compat.
          cbn in compat.
          rewrite Nat.eqb_eq in compat.
          exact compat.
        }
        rewrite <- elem_of_map_to_list in Hx. apply elem_snd in Hx.
        specialize (IH xs Hx).
        clear Hy Hx compat i y x.
        generalize dependent ys.
        induction xs as [| x xs IHxs].
        * intros; reflexivity.
        * intros ys L.
          destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
          cbn.
          f_equal.
          ** rewrite Forall_cons in IH. destruct IH as [IH _]. apply IH.
          ** cbn in L. apply eq_add_S in L. rewrite Forall_cons in IH. destruct IH as [_ IH]. specialize (IHxs IH ys L). apply IHxs.
      + f_equal. apply zip_with_idemp; intros; apply join_idemp.
      + apply ctor_compat_same_keys in compat.
        rewrite same_keys_alt in compat. unfold same_keys_alt_def in compat.
        specialize (compat i).
        rewrite Hx, Hy in compat.
        discriminate.
      + reflexivity.
    - reintros x IH y.
      cbn.
      f_equal.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite lookup_merge.
      symmetry.
      destruct (x !! i) as [x' |] eqn : Hx; destruct (y !! i) as [y' |] eqn : Hy; try reflexivity.
      cbn. f_equal. apply IH, (elem_snd i), elem_of_map_to_list, Hx.
  Qed.

  Lemma absorption_meet_join : ∀ x y, meet x (join x y) = x.
  Proof.
    intros x.
    induction x using abs_value_ind; intros y; destruct y; try reflexivity.
    all: try (cbn [join]; rewrite meet_idemp; reflexivity).
    all: try solve [ simplify_same_or; simplify_eq ].
    - cbn. rewrite Dbv.absorption_meet_join. reflexivity.
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt join xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt join xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - cbn. rewrite DZ.absorption_meet_join. reflexivity.
    - reintros xs IH ys.
      cbn. destruct (zip_with_opt join xs ys) as [xys |] eqn : H; try reflexivity.
      cbn.
      pose proof (zip_with_opt_some_length H) as [L1 [L2 L3]].
      rewrite (from_zip_with_opt L2).
      apply zip_with_opt_to_zip_with in H.
      rewrite <- H.
      f_equal.
      rewrite Forall_forall in IH.
      clear L3 L2 H xys.
      generalize dependent ys.
      induction xs as [| x xs IHxs].
      + intros. reflexivity.
      + intros ys L.
        destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
        cbn in *. apply eq_add_S in L.
        f_equal.
        * apply IH, list_elem_of_here.
        * apply (fun P => IHxs P _ L). intros x' elem y'.
          apply (IH x' (list_elem_of_further x' x xs elem) y').
    - reintros x y.
      cbn.
      f_equal.
      set_solver.
    - reintros x IH y.
      cbn.
      destruct (ctor_compat x y) eqn : compat; try reflexivity.
      rewrite (ctor_compat_merge_right ctor_compat_idemp compat).
      f_equal.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite lookup_merge.
      symmetry.
      destruct (x !! i) as [xs |] eqn : Hx; destruct (y !! i) as [ys |] eqn : Hy; cbn.
      + f_equal.
        assert (L : length xs = length ys).
        { unfold ctor_compat in compat.
          rewrite andb_true_iff in compat.
          destruct compat as [_ compat].
          rewrite forallb_forall in compat.
          rewrite <- elem_of_map_to_list, list_elem_of_In in Hx.
          specialize (compat (i, xs) Hx).
          cbn in compat.
          rewrite Hy in compat.
          cbn in compat.
          rewrite Nat.eqb_eq in compat.
          exact compat.
        }
        rewrite <- elem_of_map_to_list in Hx. apply elem_snd in Hx.
        specialize (IH xs Hx).
        clear Hy Hx compat i y x.
        generalize dependent ys.
        induction xs as [| x xs IHxs].
        * intros; reflexivity.
        * intros ys L.
          destruct ys as [| y ys]; [ cbn in L; discriminate | idtac ].
          cbn.
          f_equal.
          ** rewrite Forall_cons in IH. destruct IH as [IH _]. apply IH.
          ** cbn in L. apply eq_add_S in L. rewrite Forall_cons in IH. destruct IH as [_ IH]. specialize (IHxs IH ys L). apply IHxs.
      + f_equal. apply zip_with_idemp; intros; apply meet_idemp.
      + apply ctor_compat_same_keys in compat.
        rewrite same_keys_alt in compat. unfold same_keys_alt_def in compat.
        specialize (compat i).
        rewrite Hx, Hy in compat.
        discriminate.
      + reflexivity.
    - reintros x IH y.
      cbn.
      f_equal.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite lookup_merge.
      symmetry.
      destruct (x !! i) as [x' |] eqn : Hx; destruct (y !! i) as [y' |] eqn : Hy; try reflexivity.
      + cbn. f_equal. apply IH, (elem_snd i), elem_of_map_to_list, Hx.
      + cbn. f_equal. apply meet_idemp.
  Qed.

  Fixpoint leb (x y : value) : bool :=
    match (x, y) with
    | (V_bitvector xbv, V_bitvector ybv) => Dbv.leb xbv ybv
    | (V_vector xs, V_vector ys) => list_eqb leb xs ys
    | (V_list xs, V_list ys) => list_eqb leb xs ys
    | (V_int xi, V_int yi) => DZ.leb xi yi
    | (V_real xq, V_real yq) => xq == yq
    | (V_bool xb, V_bool yb) => xb == yb
    | (V_tuple xs, V_tuple ys) => list_eqb leb xs ys
    | (V_unit, V_unit) => true
    | (V_string xstr, V_string ystr) => xstr == ystr
    | (V_ref xid, V_ref yid) => xid == yid
    | (V_member xs, V_member ys) => if decide (xs ⊆ ys) then true else false
    | (V_ctor xm, V_ctor ym) =>
        if ctor_compat xm ym
        then map_fold (λ k ys b, b && (match xm !! k with
                                       | Some xs => list_eqb leb xs ys
                                       | None => false
                                       end))
                      true ym
        else false
    | (V_record xm, V_record ym) =>
        map_fold (λ k x b, b && (match ym !! k with
                                 | Some y => leb x y
                                 | None => false
                                 end))
                 true xm
    | (⊥, _) => true
    | (_, ⊤) => true
    | _ => false
    end.

  Definition le (x y : value) : Prop := Is_true (leb x y).

  Lemma leb_le : ∀ x y, leb x y = true ↔ le x y.
  Proof. intros. unfold le. rewrite Is_true_true. reflexivity. Qed.

  Lemma zip_with_le_join_1 : ∀ {xs ys},
    Forall (λ y : value, ∀ x : value, leb x y = true → y = join x y) xs
    → list_eqb leb ys xs = true
    → xs = zip_with join ys xs.
  Proof.
    intros xs.
    induction xs as [| x xs IH].
    - intros. rewrite zip_with_nil_r. reflexivity.
    - intros ys H L.
      destruct ys as [| y ys].
      { cbn in L. discriminate. }
      cbn in L |- *. rewrite andb_true_iff in L. destruct L as [L1 L2].
      f_equal.
      + rewrite Forall_cons in H. destruct H as [H _].
         apply (H _ L1).
      + rewrite Forall_cons in H. destruct H as [_ H].
         apply (IH ys H L2).
  Qed.

  Lemma zip_with_le_join_2 : ∀ {xs ys},
    Forall (λ y : value, ∀ x : value, join x y = y → leb x y = true) xs
    → length xs = length ys
    → xs = zip_with join ys xs
    → list_eqb leb ys xs = true.
  Proof.
    intros xs.
    induction xs as [| x xs IH].
    - intros ?? Len ?. cbn in Len.
      symmetry in Len. rewrite length_zero_iff_nil in Len. subst.
      reflexivity.
    - intros ys H Len Z.
      destruct ys as [| y ys].
      { cbn in Len. discriminate. }
      cbn in Z, Len |- *. rewrite andb_true_iff.
      split.
      + rewrite Forall_cons in H. destruct H as [H _].
        apply H. injection Z. intros. symmetry. assumption.
      + rewrite Forall_cons in H. destruct H as [_ H].
        apply eq_add_S in Len.
        injection Z. intros Z1 Z2.
        apply (IH ys H Len Z1).
  Qed.

  Lemma le_join_def_1 : ∀ x y, le x y → y = join x y.
  Proof.
    intros x y H.
    rewrite <- leb_le in H.
    generalize dependent x.
    induction y using abs_value_ind; intros x; destruct x; intros.
    all: try done.
    all: try (reintros y x H; cbn - [eqb] in H |- *; simplify_same_or; f_equal; done).
    all: try (
      reintros x IH y H;
      cbn in H |- *;
      rewrite from_zip_with_opt; [ f_equal; apply (zip_with_le_join_1 IH H) | apply (list_eqb_same_length leb H) ]
    ).
    - reintros y x H.
      cbn in H. rewrite Dbv.leb_le, Dbv.le_join_def in H.
      cbn. f_equal. exact H.
    - reintros y x H.
      cbn in H. rewrite DZ.leb_le, DZ.le_join_def in H.
      cbn. f_equal. exact H.
    - reintros y x H.
      cbn in H |- *. f_equal.
      case_decide as D.
      + symmetry. apply (subseteq_union_1_L _ _ D).
      + discriminate.
    - reintros x IH y H.
      cbn in H |- *. f_equal.
      assert (compat : ctor_compat y x = true).
      { destruct (ctor_compat y x); done. }
      rewrite compat in H |- *.
      f_equal.
      symmetry.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite map_fold_foldr in H.
      destruct (x !! i) as [xv |] eqn : Hx; destruct (y !! i) as [yv |] eqn : Hy; cbn; try reflexivity.
      + f_equal.
        rewrite <- elem_of_map_to_list in Hx.
        pose proof Hx as Hx'.
        apply list_elem_of_split in Hx.
        destruct Hx as [xs1 [xs2 Hx]].
        rewrite Hx in H.
        rewrite (SetoidList.fold_right_commutes eq_equivalence eq_equivalence) in H.
        * cbn in H. rewrite andb_true_iff in H. destruct H as [_ H]. rewrite Hy in H.
          apply elem_snd in Hx'.
          specialize (IH _ Hx').
          apply (zip_with_le_join_1 IH H).
        * unfold Proper. intros; subst; reflexivity.
        * unfold SetoidList.transpose.
          intros [k1 v1] [k2 v2] b.
          cbn.
          destruct (y !! k1); destruct (y !! k2); destruct b; cbn.
          all: repeat (rewrite andb_false_l + rewrite andb_false_r); try reflexivity.
          rewrite andb_comm. reflexivity.
      + exfalso.
        apply ctor_compat_same_keys in compat.
        rewrite <- Is_true_true, same_keys_comm in compat.
        pose proof (same_keys_none compat Hx) as L.
        rewrite Hy in L. discriminate.
    - reintros x IH y H.
      cbn in H |- *. f_equal.
      symmetry.
      apply merge_Some; try reflexivity.
      intros i.
      rewrite map_fold_foldr in H.
      destruct (x !! i) as [xv |] eqn : Hx; destruct (y !! i) as [yv |] eqn : Hy; cbn; try reflexivity.
      + f_equal.
        rewrite <- elem_of_map_to_list in Hy.
        apply list_elem_of_split in Hy.
        destruct Hy as [ys1 [ys2 Hy]].
        rewrite Hy in H.
        rewrite (SetoidList.fold_right_commutes eq_equivalence eq_equivalence) in H.
        * cbn in H. rewrite andb_true_iff in H. destruct H as [_ H]. rewrite Hx in H.
          rewrite <- elem_of_map_to_list in Hx. apply elem_snd in Hx.
          apply (IH _ Hx _ H).
        * unfold Proper. intros; subst; reflexivity.
        * unfold SetoidList.transpose.
          intros [k1 v1] [k2 v2] b.
          cbn.
          destruct (x !! k1); destruct (x !! k2); destruct b; cbn.
          all: repeat (rewrite andb_false_l + rewrite andb_false_r); try reflexivity.
          rewrite andb_comm. reflexivity.
      + exfalso.
        rewrite <- elem_of_map_to_list in Hy.
        apply list_elem_of_split in Hy.
        destruct Hy as [ys1 [ys2 Hy]].
        rewrite Hy in H.
        rewrite (SetoidList.fold_right_commutes eq_equivalence eq_equivalence) in H.
        * cbn in H. rewrite andb_true_iff in H. destruct H as [_ H]. rewrite Hx in H.
          discriminate.
        * unfold Proper. intros; subst; reflexivity.
        * unfold SetoidList.transpose.
          intros [k1 v1] [k2 v2] b.
          cbn.
          destruct (x !! k1); destruct (x !! k2); destruct b; cbn.
          all: repeat (rewrite andb_false_l + rewrite andb_false_r); try reflexivity.
          rewrite andb_comm. reflexivity.
  Qed.

  Lemma foldr_uncurry_to_forallb : ∀ {A B} {P : A → B → bool} {xs : list (A * B)},
    foldr (uncurry (λ x y b, b && P x y)) true xs = forallb (uncurry P) xs.
  Proof.
    intros A B P xs.
    induction xs as [| x xs IH].
    - reflexivity.
    - cbn. rewrite IH.
      rewrite andb_comm. unfold uncurry. destruct_match. reflexivity.
  Qed.

  Lemma le_join_def_2 : ∀ x y, y = join x y → le x y.
  Proof.
    intros x y H.
    rewrite <- leb_le.
    symmetry in H.
    generalize dependent x.
    induction y using abs_value_ind; intros x; destruct x; intros.
    all: try done.
    all: try solve [ cbn - [eqb] in *; simplify_same_or ].
    all: try (
      reintros y IH x H;
      cbn in H |- *;
      destruct (zip_with_opt join x y) eqn : E; cbn in H; [ idtac | discriminate ];
      pose proof (zip_with_opt_some_length E) as [L1 [L2 L3]];
      apply zip_with_opt_to_zip_with in E;
      injection H; clear H; intros H; subst;
      apply (zip_with_le_join_2 IH (eq_sym L1) (eq_sym H))
    ).
    - reintros y x H. cbn in *. injection H.
      rewrite Dbv.leb_le, Dbv.le_join_def. done.
    - reintros y x H. cbn in *. injection H.
      rewrite DZ.leb_le, DZ.le_join_def. done.
    - reintros x y H. cbn in *.
      case_decide.
      + reflexivity.
      + exfalso. inversion H. set_solver.
    - reintros y IH x H.
      cbn in H |- *.
      destruct (ctor_compat x y) eqn : E; [ idtac | discriminate ].
      injection H. clear H. intros H.
      rewrite map_fold_foldr.
      rewrite <- merge_Some in H; [ idtac | reflexivity ].
      rewrite foldr_uncurry_to_forallb, forallb_forall.
      intros [k v] In. unfold uncurry.
      specialize (H k).
      rewrite <- list_elem_of_In in In.
      pose proof In as In'.
      apply elem_snd in In.
      rewrite elem_of_map_to_list in In'.
      specialize (IH v In).
      destruct (y !! k) as [ys |] eqn : Hy; destruct (x !! k) as [xs |] eqn : Hx; cbn in H; try discriminate.
      + apply (zip_with_le_join_2 IH); inversion In'; subst.
        * rewrite ctor_compat_comm in E.
          apply (ctor_compat_same_length k E Hy Hx).
        * injection H. intros. assumption.
      + apply ctor_compat_same_keys in E.
        rewrite <- Is_true_true in E.
        pose proof (same_keys_none E Hx) as L.
        rewrite L in Hy. discriminate.
    - reintros y IH x H.
      cbn in H |- *.
      injection H. clear H. intros H.
      rewrite map_fold_foldr.
      rewrite <- merge_Some in H; [ idtac | reflexivity ].
      rewrite foldr_uncurry_to_forallb, forallb_forall.
      intros [k xs] Hx. unfold uncurry.
      specialize (H k).
      rewrite <- list_elem_of_In, elem_of_map_to_list in Hx.
      rewrite Hx in H.
      destruct (y !! k) as [ys |] eqn : Hy; cbn in H; try discriminate.
      rewrite <- elem_of_map_to_list in Hy.
      apply elem_snd in Hy.
      apply Some_inj in H. symmetry in H.
      apply (IH ys Hy xs H).
  Qed.

  Lemma le_join_def : ∀ x y, le x y ↔ y = join x y.
  Proof. intros. split; [ apply le_join_def_1 | apply le_join_def_2 ]. Qed.

  Fixpoint α (x : Ast.value) : value :=
    match x with
    | Ast.V_bitvector bv => V_bitvector (Dbv.α bv)
    | Ast.V_vector xs => V_vector (List.map α xs)
    | Ast.V_list xs => V_list (List.map α xs)
    | Ast.V_int i => V_int (DZ.α i)
    | Ast.V_real q => V_real (Q2Qc q)
    | Ast.V_bool b => V_bool b
    | Ast.V_tuple xs => V_tuple (List.map α xs)
    | Ast.V_unit => V_unit
    | Ast.V_string str => V_string str
    | Ast.V_ref id => V_ref (Aux.unwrap id)
    | Ast.V_member id => V_member {[ Aux.unwrap id ]}
    | Ast.V_ctor id xs => V_ctor {[ Aux.unwrap id := List.map α xs ]}
    | Ast.V_record fields => V_record (foldl (λ m '(k, v), <[Aux.unwrap k := α v]> m) ∅ fields)
    end.

  Definition of_lit (l : Ast.lit) : value := α (ValueType.value_of_lit l).

  Definition lookup_field (r : value) (name : Ast.id_aux) : value :=
    match r with
    | V_record m => from_option (λ x, x) ⊥ (m !! name)
    | _ => ⊥
    end.

  Definition complete (b : PatternMatch.binding t) : t := ⊥.
End Dom.
