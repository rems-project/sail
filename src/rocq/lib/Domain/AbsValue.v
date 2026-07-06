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
From stdpp Require Import mapset.
From stdpp Require Import bitvector.definitions.
From stdpp Require Import list.

From Sail Require Import SailBase.
From Sail Require Import Assignment.
From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import OptionUtil.
From Sail Require Import Tactics.
From Sail Require Import Domain.Lattice.
From Sail Require Domain.AbsBitvector.
From Sail Require Import BitList.
From Sail Require Import Bit.
From Sail Require Domain.Interval.
From Sail Require Ast.
From Sail Require PatternMatch.
From Sail Require ValueType.

Import Ltac2.Std.

Module Dom (DZ : SAIL_INT) (Dbv : SAIL_BITS) (T : SAIL_BITS_INT Dbv DZ) <: SAIL_VALUE.
  Module DZP := DomainProperties BinInt.Z DZ.
  Module DbvP := DomainProperties Lattice.Bits Dbv.

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

  Definition mk_ctor (s : Ast.id_aux) (args : list value) : value :=
    V_ctor {[ s := args ]}.

  Definition mk_member (s : Ast.id_aux) : value := V_member {[ s ]}.

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

  Definition mk_unit (_ : unit) : value := V_unit.

  Definition mk_tuple : list value → value := V_tuple.

  Definition mk_list : list value → value := V_list.

  Definition mk_vector : list value → value := V_vector.

  Definition mk_ref (id : Ast.id_aux) := V_ref id.

  Definition cons (h : value) (t : value) : value :=
    match t with
    | V_list ts => V_list (h :: ts)
    | _ => V_bot
    end.

  Definition t := value.

  Definition top := V_top.
  Notation "⊤" := V_top.

  Definition bot : t := V_bot.
  Notation "⊥" := V_bot.

  Definition value_length (v : value) : value :=
    match v with
    | V_bitvector bv => V_int (T.bits_length bv)
    | V_list vs => V_int (DZ.α (Z.of_nat (length vs)))
    | V_vector vs => V_int (DZ.α (Z.of_nat (length vs)))
    | _ => V_bot
    end.

  (** Construct a bitvector from a list of bit values. *)
  Definition mk_bitvector' (vs : list value) : option Dbv.t :=
    fold_left
      (fun acc v =>
        match (acc, v) with
        | (Some acc', V_bitvector bv) => Some (Dbv.append acc' (Dbv.meet bv Dbv.unknown_bit))
        | _ => None
        end
      )
      vs
      (Some Dbv.zwbv).

  Definition mk_bitvector (vs : list value) : value :=
    match mk_bitvector' vs with
    | Some bv => V_bitvector bv
    | None => V_bot
    end.

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

  Definition key_inter {V}
    (m1 m2 : gmap Ast.id_aux V) : list Ast.id_aux :=
    map fst (filter (fun '(k, _) => bool_decide (k ∈ dom m2)) (map_to_list m1)).

  Lemma key_inter_some : ∀ {V} {x y : gmap Ast.id_aux V} k {v1 v2}, x !! k = Some v1 → y !! k = Some v2 → k ∈ key_inter x y.
  Proof.
    intros V x y k v1 v2 Hx Hy.
    unfold key_inter.
    rewrite list_elem_of_fmap.
    exists (k, v1). split; [ reflexivity | ].
    rewrite list_elem_of_filter. split.
    - apply bool_decide_pack. rewrite elem_of_dom. exists v2. exact Hy.
    - rewrite elem_of_map_to_list. exact Hx.
  Qed.

  Lemma key_inter_refl : ∀ {V} {x : gmap Ast.id_aux V} k, k ∈ key_inter x x → ∃v, x !! k = Some v.
  Proof.
    intros V x k Hk.
    unfold key_inter in Hk.
    rewrite list_elem_of_fmap in Hk.
    destruct Hk as [[k' v] [Hfst Hfin]].
    cbn in Hfst. subst k'.
    rewrite list_elem_of_filter in Hfin.
    destruct Hfin as [_ Hxin].
    rewrite elem_of_map_to_list in Hxin.
    exists v. exact Hxin.
  Qed.

  Definition ctor_compat (x y : gmap Ast.id_aux (list value)) : bool :=
    forallb (λ k, match (x !! k, y !! k) with
                  | (Some vx, Some vy) => length vx =? length vy
                  | _ => true
                  end)
            (key_inter x y).

  Lemma ctor_compat_same_length : ∀ {x y} k {xs ys},
    ctor_compat x y = true → x !! k = Some xs → y !! k = Some ys → length xs = length ys.
  Proof.
    intros x y k xs ys compat Hx Hy.
    unfold ctor_compat in compat.
    rewrite forallb_forall in compat.
    assert (L : In k (key_inter x y)).
    { rewrite <- list_elem_of_In. apply (key_inter_some k Hx Hy). }
    specialize (compat k L).
    rewrite Hx, Hy, Nat.eqb_eq in compat.
    exact compat.
  Qed.

  Lemma ctor_compat_idemp : ∀ {x}, ctor_compat x x = true.
  Proof.
    intros x.
    unfold ctor_compat. rewrite forallb_forall.
    intros k In.
    rewrite <- list_elem_of_In in In.
    apply (key_inter_refl k) in In.
    destruct In as [v In].
    rewrite In, Nat.eqb_eq.
    reflexivity.
  Qed.

  Lemma ctor_compat_comm : ∀ x y, ctor_compat x y = ctor_compat y x.
  Proof.
    intros x y.
    destruct (ctor_compat x y) eqn:Hxy; destruct (ctor_compat y x) eqn:Hyx; try reflexivity; exfalso.
    - unfold ctor_compat in Hyx.
      rewrite forallb_false_iff in Hyx.
      destruct Hyx as [k [Hk Hfalse]].
      unfold key_inter in Hk.
      rewrite list_elem_of_fmap in Hk.
      destruct Hk as [[k' vy] [Hfst Hfin]].
      cbn in Hfst. subst k'.
      rewrite list_elem_of_filter in Hfin.
      destruct Hfin as [Hdom Hyin].
      apply bool_decide_unpack, elem_of_dom in Hdom.
      destruct Hdom as [vx Hvx].
      rewrite elem_of_map_to_list in Hyin.
      rewrite Hyin, Hvx in Hfalse.
      apply Nat.eqb_neq in Hfalse.
      apply Hfalse. symmetry.
      exact (ctor_compat_same_length k Hxy Hvx Hyin).
    - unfold ctor_compat in Hxy.
      rewrite forallb_false_iff in Hxy.
      destruct Hxy as [k [Hk Hfalse]].
      unfold key_inter in Hk.
      rewrite list_elem_of_fmap in Hk.
      destruct Hk as [[k' vx] [Hfst Hfin]].
      cbn in Hfst. subst k'.
      rewrite list_elem_of_filter in Hfin.
      destruct Hfin as [Hdom Hxin].
      apply bool_decide_unpack, elem_of_dom in Hdom.
      destruct Hdom as [vy Hvy].
      rewrite elem_of_map_to_list in Hxin.
      rewrite Hxin, Hvy in Hfalse.
      apply Nat.eqb_neq in Hfalse.
      apply Hfalse. symmetry.
      exact (ctor_compat_same_length k Hyx Hvy Hxin).
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

  Lemma ctor_compat_of_forall : ∀ {x y : gmap Ast.id_aux (list value)},
    (∀ k vx vy, x !! k = Some vx → y !! k = Some vy → length vx = length vy) →
    ctor_compat x y = true.
  Proof.
    intros x y H.
    unfold ctor_compat. rewrite forallb_forall.
    intros k Hk.
    rewrite <- list_elem_of_In in Hk.
    unfold key_inter in Hk.
    rewrite list_elem_of_fmap in Hk.
    destruct Hk as [[k' vx] [Hfst Hfin]].
    cbn in Hfst. subst k'.
    rewrite list_elem_of_filter in Hfin.
    destruct Hfin as [Hdom_y Hxin].
    apply bool_decide_unpack, elem_of_dom in Hdom_y.
    destruct Hdom_y as [vy Hvy].
    rewrite elem_of_map_to_list in Hxin.
    rewrite Hxin, Hvy, Nat.eqb_eq.
    exact (H k vx vy Hxin Hvy).
  Qed.

  Lemma ctor_compat_false_witness : ∀ {x y : gmap Ast.id_aux (list value)} {k vx vy},
    x !! k = Some vx → y !! k = Some vy → length vx ≠ length vy →
    ctor_compat x y = false.
  Proof.
    intros x y k vx vy Hx Hy Hlen.
    unfold ctor_compat. rewrite forallb_false_iff.
    exists k. split.
    - exact (key_inter_some k Hx Hy).
    - rewrite Hx, Hy, Nat.eqb_neq. exact Hlen.
  Qed.

  Lemma ctor_compat_merge_false_left : ∀ {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = true → ctor_compat y z = false →
    ctor_compat (merge (option_join (zip_with join)) x y) z = false.
  Proof.
    intros x y z Hxy Hyz.
    unfold ctor_compat in Hyz. rewrite forallb_false_iff in Hyz.
    destruct Hyz as [k [Hk Hkfalse]].
    unfold key_inter in Hk. rewrite list_elem_of_fmap in Hk.
    destruct Hk as [[k' vy] [Hfst Hfin]].
    cbn in Hfst. subst k'.
    rewrite list_elem_of_filter in Hfin.
    destruct Hfin as [Hdom_z Hyin].
    apply bool_decide_unpack, elem_of_dom in Hdom_z.
    destruct Hdom_z as [vz Hvz].
    rewrite elem_of_map_to_list in Hyin.
    rewrite Hyin, Hvz in Hkfalse. apply Nat.eqb_neq in Hkfalse.
    destruct (x !! k) as [vx |] eqn:Hvx.
    - apply (ctor_compat_false_witness (k := k) (vx := zip_with join vx vy) (vy := vz)).
      + rewrite lookup_merge, Hvx, Hyin. reflexivity.
      + exact Hvz.
      + rewrite (length_zip_with_l_eq join vx vy (ctor_compat_same_length k Hxy Hvx Hyin)).
        rewrite (ctor_compat_same_length k Hxy Hvx Hyin). exact Hkfalse.
    - apply (ctor_compat_false_witness (k := k) (vx := vy) (vy := vz)).
      + rewrite lookup_merge, Hvx, Hyin. reflexivity.
      + exact Hvz.
      + exact Hkfalse.
  Qed.

  Lemma ctor_compat_merge_false_right : ∀ {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = false → ctor_compat y z = true →
    ctor_compat x (merge (option_join (zip_with join)) y z) = false.
  Proof.
    intros x y z Hxy Hyz.
    unfold ctor_compat in Hxy. rewrite forallb_false_iff in Hxy.
    destruct Hxy as [k [Hk Hkfalse]].
    unfold key_inter in Hk. rewrite list_elem_of_fmap in Hk.
    destruct Hk as [[k' vx] [Hfst Hfin]].
    cbn in Hfst. subst k'.
    rewrite list_elem_of_filter in Hfin.
    destruct Hfin as [Hdom_y Hxin].
    apply bool_decide_unpack, elem_of_dom in Hdom_y.
    destruct Hdom_y as [vy Hvy].
    rewrite elem_of_map_to_list in Hxin.
    rewrite Hxin, Hvy in Hkfalse. apply Nat.eqb_neq in Hkfalse.
    destruct (z !! k) as [vz |] eqn:Hvz.
    - apply (ctor_compat_false_witness (k := k) (vx := vx) (vy := zip_with join vy vz)).
      + exact Hxin.
      + rewrite lookup_merge, Hvy, Hvz. reflexivity.
      + rewrite (length_zip_with_l_eq join vy vz (ctor_compat_same_length k Hyz Hvy Hvz)).
        exact Hkfalse.
    - apply (ctor_compat_false_witness (k := k) (vx := vx) (vy := vy)).
      + exact Hxin.
      + rewrite lookup_merge, Hvy, Hvz. reflexivity.
      + exact Hkfalse.
  Qed.

  Lemma ctor_compat_merge_eq : ∀ {x y z : gmap Ast.id_aux (list value)},
    ctor_compat x y = true → ctor_compat y z = true →
    ctor_compat x (merge (option_join (zip_with join)) y z) =
    ctor_compat (merge (option_join (zip_with join)) x y) z.
  Proof.
    intros x y z Hxy Hyz.
    apply Bool.eq_iff_eq_true. split; intro H; apply ctor_compat_of_forall.
    - intros k vxy vz H_mxy Hvz.
      rewrite lookup_merge in H_mxy.
      destruct (y !! k) as [vy |] eqn:Hvy; destruct (x !! k) as [vx |] eqn:Hvx;
      cbn in H_mxy; try discriminate; injection H_mxy as H_mxy; subst.
      + rewrite (length_zip_with_l_eq join vx vy (ctor_compat_same_length k Hxy Hvx Hvy)).
        rewrite (ctor_compat_same_length k Hxy Hvx Hvy).
        exact (ctor_compat_same_length k Hyz Hvy Hvz).
      + exact (ctor_compat_same_length k Hyz Hvy Hvz).
      + assert (Hmyz : (merge (option_join (zip_with join)) y z) !! k = Some vz).
        { rewrite lookup_merge, Hvy, Hvz. reflexivity. }
        exact (ctor_compat_same_length k H Hvx Hmyz).
    - intros k vx vyz Hvx H_myz.
      rewrite lookup_merge in H_myz.
      destruct (y !! k) as [vy |] eqn:Hvy; destruct (z !! k) as [vz |] eqn:Hvz;
      cbn in H_myz; try discriminate; injection H_myz as H_myz; subst.
      + rewrite (length_zip_with_l_eq join vy vz (ctor_compat_same_length k Hyz Hvy Hvz)).
        exact (ctor_compat_same_length k Hxy Hvx Hvy).
      + exact (ctor_compat_same_length k Hxy Hvx Hvy).
      + assert (Hmxy : (merge (option_join (zip_with join)) x y) !! k = Some vx).
        { rewrite lookup_merge, Hvx, Hvy. reflexivity. }
        exact (ctor_compat_same_length k H Hmxy Hvz).
  Qed.

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
      destruct (ctor_compat x y) eqn:Hxy; destruct (ctor_compat y z) eqn:Hyz; cbn.
      + rewrite (ctor_compat_merge_eq Hxy Hyz).
        destruct (ctor_compat (merge (option_join (zip_with join)) x y) z).
        * f_equal. apply merge_assoc. intros i.
          destruct (x !! i) as [xs |]; destruct (y !! i) as [ys |] eqn:HY; destruct (z !! i) as [zs |]; cbn; try reflexivity.
          f_equal. apply zip_with_assoc. intros x' y' z' _ Hy' _.
          assert (Lys : ys ∈ map snd (map_to_list y)).
          { apply (elem_snd i). rewrite elem_of_map_to_list. exact HY. }
          specialize (IH ys Lys). rewrite Forall_forall in IH.
          exact (IH y' Hy' x' z').
        * reflexivity.
      + rewrite (ctor_compat_merge_false_left Hxy Hyz). reflexivity.
      + rewrite (ctor_compat_merge_false_right Hxy Hyz). reflexivity.
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
    | (V_ctor m₁, V_ctor m₂) =>
        V_ctor (merge (λ o₁ o₂, match o₁, o₂ with
                                 | Some l₁, Some l₂ =>
                                     if length l₁ =? length l₂
                                     then Some (zip_with meet l₁ l₂)
                                     else None
                                 | _, _ => None
                                 end) m₁ m₂)
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
      cbn. f_equal.
      apply merge_idemp.
      intros i.
      destruct (x !! i) as [xs |] eqn : Hx; cbn; try reflexivity.
      rewrite Nat.eqb_refl. f_equal.
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
      cbn. f_equal.
      apply merge_comm.
      intros id.
      destruct (x !! id) as [xs |] eqn : XH;
      destruct (y !! id) as [ys |]; try reflexivity.
      cbn. rewrite Nat.eqb_sym.
      destruct (length ys =? length xs); try reflexivity.
      f_equal.
      apply zip_with_comm. intros ?? In_xs ?.
      specialize (IH xs).
      assert (L : xs ∈ map snd (map_to_list x)).
      { apply (elem_snd id), elem_of_map_to_list, XH. }
      specialize (IH L).
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
      cbn. f_equal.
      apply merge_assoc. intros i.
      destruct (x !! i) as [xs |]; destruct (y !! i) as [ys |] eqn:HY; destruct (z !! i) as [zs |]; cbn;
        try reflexivity; try (destruct (length _ =? length _); reflexivity).
      destruct (length xs =? length ys) eqn:Hxy; cbn.
      + apply Nat.eqb_eq in Hxy.
        rewrite (length_zip_with_l_eq meet xs ys Hxy).
        destruct (length ys =? length zs) eqn:Hyz; cbn.
        * apply Nat.eqb_eq in Hyz.
          rewrite (length_zip_with_l_eq meet ys zs Hyz).
          rewrite (proj2 (Nat.eqb_eq _ _) (eq_trans Hxy Hyz)).
          rewrite (proj2 (Nat.eqb_eq _ _) Hxy). f_equal.
          apply zip_with_assoc. intros x' y' z' _ Hy' _.
          assert (Lys : ys ∈ map snd (map_to_list y)).
          { apply (elem_snd i). rewrite elem_of_map_to_list. exact HY. }
          specialize (IH ys Lys). rewrite Forall_forall in IH.
          exact (IH y' Hy' x' z').
        * rewrite Nat.eqb_neq in Hyz.
          rewrite (proj2 (Nat.eqb_neq _ _) (fun H => Hyz (eq_trans (eq_sym Hxy) H))). reflexivity.
      + destruct (length ys =? length zs) eqn:Hyz; cbn; try reflexivity.
        apply Nat.eqb_eq in Hyz.
        rewrite (length_zip_with_l_eq meet ys zs Hyz).
        rewrite Hxy. reflexivity.
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
      assert (Hcompat : ctor_compat x (merge (λ o₁ o₂, match o₁, o₂ with
        | Some l₁, Some l₂ => if length l₁ =? length l₂ then Some (zip_with meet l₁ l₂) else None
        | _, _ => None end) x y) = true).
      { apply ctor_compat_of_forall. intros k vx vm Hvx Hm.
        rewrite lookup_merge, Hvx in Hm.
        destruct (y !! k) as [vy |]; cbn in Hm; try discriminate.
        destruct (length vx =? length vy) eqn:Hlxy; cbn in Hm; try discriminate.
        injection Hm as Hm. subst.
        apply Nat.eqb_eq in Hlxy.
        exact (eq_sym (length_zip_with_l_eq meet vx vy Hlxy)). }
      rewrite Hcompat. f_equal.
      apply merge_Some; try reflexivity.
      intros i. rewrite lookup_merge.
      destruct (x !! i) as [xs |] eqn:Hx; cbn; try reflexivity;
        try (destruct (y !! i); reflexivity).
      destruct (y !! i) as [ys |]; cbn; try reflexivity.
      destruct (length xs =? length ys) eqn:Hxy; cbn; try reflexivity.
      apply Nat.eqb_eq in Hxy.
      f_equal.
      assert (IH_xs : Forall (λ v, ∀ w, join v (meet v w) = v) xs).
      { apply IH.
        apply (elem_snd i).
        rewrite elem_of_map_to_list. exact Hx. }
      rewrite Forall_forall in IH_xs.
      clear IH Hcompat i Hx x y.
      revert ys Hxy.
      induction xs as [| x' xs' IHxs'].
      + intros. reflexivity.
      + intros ys' Lxy'.
        destruct ys' as [| y' ys'']; [cbn in Lxy'; discriminate|].
        cbn in Lxy' |- *. apply eq_add_S in Lxy'.
        f_equal.
        * symmetry. apply IH_xs, list_elem_of_here.
        * apply IHxs'.
          { intros v Hv. exact (IH_xs v (list_elem_of_further _ _ _ Hv)). }
          { exact Lxy'. }
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
      f_equal.
      apply merge_Some; try reflexivity.
      intros i. rewrite lookup_merge.
      destruct (x !! i) as [xs |] eqn:Hx; cbn; try reflexivity.
      destruct (y !! i) as [ys |] eqn:Hy; cbn.
      + assert (Hlxy : length xs = length ys) by exact (ctor_compat_same_length i compat Hx Hy).
        rewrite (proj2 (Nat.eqb_eq _ _) (eq_sym (length_zip_with_l_eq join xs ys Hlxy))).
        f_equal.
        assert (IH_xs : Forall (λ v, ∀ w, meet v (join v w) = v) xs).
        { apply IH. apply (elem_snd i). rewrite elem_of_map_to_list. exact Hx. }
        rewrite Forall_forall in IH_xs.
        clear IH compat i Hx Hy x y.
        revert ys Hlxy IH_xs.
        induction xs as [| x' xs' IHxs'].
        { intros. reflexivity. }
        intros ys' Hlxy' IH_xs'.
        destruct ys' as [| y' ys'']; [cbn in Hlxy'; discriminate|].
        cbn in Hlxy' |- *. apply eq_add_S in Hlxy'.
        f_equal.
        * symmetry. exact (IH_xs' x' (list_elem_of_here x' xs') y').
        * apply IHxs'.
          { exact Hlxy'. }
          { intros v Hv. exact (IH_xs' v (list_elem_of_further _ _ _ Hv)). }
      + rewrite Nat.eqb_refl. f_equal.
        symmetry. apply zip_with_idemp. intros v _. apply meet_idemp.
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
        then map_fold (λ k xs b, b && (match ym !! k with
                                       | Some ys => list_eqb leb xs ys
                                       | None => false
                                       end))
                      true xm
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
        rewrite <- elem_of_map_to_list in Hy.
        apply list_elem_of_split in Hy.
        destruct Hy as [ys1 [ys2 Hy]].
        rewrite Hy in H.
        rewrite (SetoidList.fold_right_commutes eq_equivalence eq_equivalence) in H.
        * cbn in H. rewrite andb_true_iff in H. destruct H as [_ H]. rewrite Hx in H.
          rewrite <- elem_of_map_to_list in Hx.
          apply elem_snd in Hx.
          specialize (IH _ Hx).
          apply (zip_with_le_join_1 IH H).
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
      rewrite <- list_elem_of_In, elem_of_map_to_list in In.
      rewrite In in H.
      destruct (y !! k) as [ys |] eqn : Hy; cbn in H; try discriminate.
      apply Some_inj in H.
      assert (Hys : ys ∈ map snd (map_to_list y)).
      { apply (elem_snd k). rewrite elem_of_map_to_list. exact Hy. }
      apply (zip_with_le_join_2 (IH ys Hys) (eq_sym (ctor_compat_same_length k E In Hy)) H).
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

  Fixpoint abst (x : Ast.value) : value :=
    match x with
    | Ast.V_bitvector bv => V_bitvector (Dbv.α (Bit.Bits.to_bvn bv))
    | Ast.V_vector xs => V_vector (List.map abst xs)
    | Ast.V_list xs => V_list (List.map abst xs)
    | Ast.V_int i => V_int (DZ.α i)
    | Ast.V_real q => V_real (Q2Qc q)
    | Ast.V_bool b => V_bool b
    | Ast.V_tuple xs => V_tuple (List.map abst xs)
    | Ast.V_unit => V_unit
    | Ast.V_string str => V_string str
    | Ast.V_ref id => V_ref (Aux.unwrap id)
    | Ast.V_member id => V_member {[ Aux.unwrap id ]}
    | Ast.V_ctor id xs => V_ctor {[ Aux.unwrap id := List.map abst xs ]}
    | Ast.V_record fields => V_record (foldl (λ m '(k, v), <[Aux.unwrap k := abst v]> m) ∅ fields)
    end.

  Notation α := abst.

  Definition of_lit (l : Ast.lit) : value := α (ValueType.value_of_lit l).

  Definition lookup_field (r : value) (name : Ast.id_aux) : value :=
    match r with
    | V_record m => from_option (λ x, x) ⊥ (m !! name)
    | _ => ⊥
    end.

  (** Like [lookup_field], but degrading to [⊤] rather than [⊥]: used when
      descending an assignment path, where an absent field just means
      uninitialised storage (mirroring [get_vector_elem]). *)
  Definition get_field (r : value) (name : Ast.id_aux) : value :=
    match r with
    | V_record m => from_option (λ x, x) ⊤ (m !! name)
    | _ => ⊤
    end.

  (** Build a record value from a list of (field, value) pairs. Later
      duplicate fields win, matching [abst]'s [V_record] case. *)
  Definition mk_record (fs : list (Ast.id_aux * value)) : value :=
    V_record (foldl (λ m '(k, v), <[k := v]> m) ∅ fs).

  (** Replace fields of a known record value; [None] when the base isn't a
      known record. *)
  Definition update_record (r : value) (fs : list (Ast.id_aux * value)) : option value :=
    match r with
    | V_record m => Some (V_record (foldl (λ m '(k, v), <[k := v]> m) m fs))
    | _ => None
    end.

  (** Concretisers so callers that only see [L] (not [DZ] / [Dbv]) can pin
      down concrete singletons. *)
  Definition concrete_int (v : value) : option Z :=
    match v with
    | V_int i => DZ.concrete i
    | _ => None
    end.

  Definition concrete_ref (v : value) : option Ast.id_aux :=
    match v with
    | V_ref id => Some id
    | _ => None
    end.

  Definition concrete_bv_length (v : value) : option Z :=
    match v with
    | V_bitvector bv => DZ.concrete (T.bits_length bv)
    | _ => None
    end.

  Definition tuple_elems (v : value) : option (list value) :=
    match v with
    | V_tuple vs => Some vs
    | _ => None
    end.

  (** Extract bits [s..s+m-1] (0-based, LSB at index 0) of a [V_bitvector].
      Wraps [Dbv.slice] so [Residual] can stay agnostic to [Dbv]. *)
  Definition bv_slice (v : value) (s m : N) : value :=
    match v with
    | V_bitvector bv => V_bitvector (Dbv.slice bv s m)
    | _ => V_top
    end.

  (** Update field [k] of a record value to [v]. An uninitialised [V_top]
      register is treated as an empty record (matching [apply_field_path]'s
      behaviour). Anything else degrades to [⊤] — we lose the value but
      the residual still records the write. *)
  Definition set_field (r : value) (k : Ast.id_aux) (v : value) : value :=
    match r with
    | V_record m => V_record (insert k v m)
    | V_top => V_record (insert k v ∅)
    | _ => V_top
    end.

  (** Replace the element at [i] of a [V_vector]. Out-of-bounds indices and
      non-vector bases degrade to [⊤]. *)
  Fixpoint vector_update (vs : list value) (i : nat) (v : value) : list value :=
    match vs, i with
    | [], _ => []
    | x :: rest, O => v :: rest
    | x :: rest, S n => x :: vector_update rest n v
    end.

  (** Set bits [lo..hi] (inclusive, [Order dec] convention) of a [V_bitvector]
      to [new]. Splits the base into [high ‖ middle ‖ low] using [Dbv.slice],
      then reassembles [high ‖ new ‖ low] via [Dbv.append]. Degrades to [⊤]
      if the base has unknown width, the bounds are out of range, or the
      base / [new] aren't both [V_bitvector]. *)
  Definition set_bv_range (base : value) (hi lo : Z) (new : value) : value :=
    match base, new with
    | V_bitvector bv_base, V_bitvector bv_new =>
        match DZ.concrete (T.bits_length bv_base) with
        | Some n_z =>
            if andb (Z.leb 0 lo) (andb (Z.leb lo hi) (Z.ltb hi n_z)) then
              let n_N := Z.to_N n_z in
              let lo_N := Z.to_N lo in
              let hi_N := Z.to_N hi in
              let high_start := (hi_N + 1)%N in
              let high_width := (n_N - high_start)%N in
              let high_part := Dbv.slice bv_base high_start high_width in
              let low_part := Dbv.slice bv_base 0%N lo_N in
              V_bitvector (Dbv.append high_part (Dbv.append bv_new low_part))
            else V_top
        | None => V_top
        end
    | _, _ => V_top
    end.

  (** Read / set element at (Sail-level) index [i] of a [V_vector]. We
      follow the [dec] convention used by [access] / [update_list] in
      [Sail_lib]: a vector of length [N] stores list position [N - 1 - i]
      when the source writes [v[i]]. (Sail's default [Order dec] covers
      nearly all real code; [inc]-ordered models would be off-by-mirror
      — fix the storage convention once we plumb the order into the
      annotation.) *)
  Definition get_vector_elem (xs : value) (i : Z) : value :=
    match xs with
    | V_vector vs =>
        let n := Z.of_nat (length vs) in
        if andb (Z.leb 0 i) (Z.ltb i n) then
          match nth_error vs (Z.to_nat (n - 1 - i)) with Some x => x | None => V_top end
        else V_top
    | _ => V_top
    end.

  Definition set_vector_elem (xs : value) (i : Z) (v : value) : value :=
    match xs with
    | V_vector vs =>
        let n := Z.of_nat (length vs) in
        if andb (Z.leb 0 i) (Z.ltb i n) then
          V_vector (vector_update vs (Z.to_nat (n - 1 - i)) v)
        else V_top
    (* [bits(N)][i] = bit-valued RHS: forward to [set_bv_range] with
       [hi = lo = i]. Sail's [bit] is a 1-element bitvector at runtime, so
       [v] is itself a [V_bitvector]. *)
    | V_bitvector _ => set_bv_range xs i i v
    | _ => V_top
    end.

  Module Matching (Tannot : TypeAnnot.S).
    Import PatternMatch.

    (** Compare a concrete bitvector literal [lit_bs] against an abstract
        [V_bitvector] value [bv]. Matched only when [bv] is exactly the
        singleton {[lit_bs]}; MaybeMatched when [lit_bs] is one of the
        values [bv] admits; otherwise Unmatched. *)
    Definition match_bitvector_lit (lit_bs : list Bit.bit) (bv : Dbv.t) : match_result value :=
      let lit_bv := Dbv.α (Bit.Bits.to_bvn lit_bs) in
      if Dbv.leb lit_bv bv then
        if Dbv.leb bv lit_bv then simple_match value
        else MaybeMatched (empty_bindings value)
      else Unmatched.

    Definition pattern_match_literal (l : Ast.lit) (v : value) : match_result value :=
      let 'Ast.L_aux aux annot := l in
      match (aux, v) with
      | (Ast.L_unit,      V_unit        ) => simple_match value
      | (Ast.L_true,      V_bool true   ) => simple_match value
      | (Ast.L_false,     V_bool false  ) => simple_match value
      | (Ast.L_num n,     V_int m       ) =>
          (* If the interval contains [n] AND admits only [n], Match. If [n] is
             one of several admitted values, MaybeMatched. Otherwise Unmatched.
             We approximate "admits only [n]" by checking [leb (α n) m] both
             ways. *)
          if DZ.leb (DZ.α n) m then
            if DZ.leb m (DZ.α n) then simple_match value
            else MaybeMatched (empty_bindings value)
          else Unmatched
      | (Ast.L_hex s,     V_bitvector vs) => match_bitvector_lit (of_hex_lit s) vs
      | (Ast.L_bin s,     V_bitvector vs) => match_bitvector_lit (of_bin_lit s) vs
      | (Ast.L_string s1, V_string s2   ) => simple_match_when value (String.eqb s1 s2)
      | (Ast.L_real r1,   V_real r2     ) => simple_match_when value (QArith_base.Qeq_bool r1 r2)
      | _ => Unmatched
      end.

    (** Pattern match against the abstract value [v]. We handle the cases that
        matter for let-bindings and the simple tuple/constructor matches used
        across the test suite; anything we don't understand defaults to
        [simple_match] (matched with no bindings), which is the same stub
        behaviour we had before. *)
    Fixpoint pattern_match (p : Ast.pat Tannot.t) (v : value) {struct p} : match_result value :=
      let 'Ast.P_aux aux _ := p in
      match aux with
      | Ast.P_lit lit => pattern_match_literal lit v
      | Ast.P_wild => simple_match value
      | Ast.P_id id =>
          (* In Sail, an identifier in a pattern can be a fresh variable
             binding, an enum member, or a nullary union constructor. The
             typechecker tells us which via [get_id_type]. *)
          let 'Ast.P_aux _ annot := p in
          match Tannot.get_id_type (snd annot) id with
          | TypeAnnot.Types.Enum_member =>
              match v with
              | V_member ids =>
                  if bool_decide (Aux.unwrap id ∈ ids) then
                    if Nat.eqb (size ids) 1 then simple_match value
                    else MaybeMatched (empty_bindings value)
                  else Unmatched
              | V_top => MaybeMatched (empty_bindings value)
              | _ => Unmatched
              end
          | _ => add_match id (Complete v) (simple_match value)
          end
      | Ast.P_typ _ p' => pattern_match p' v
      | Ast.P_var p' _ => pattern_match p' v
      | Ast.P_as p' id =>
          add_match id (Complete v) (pattern_match p' v)
      | Ast.P_tuple ps =>
          match v with
          | V_unit =>
              match ps with [] => simple_match value | _ => Unmatched end
          | V_tuple vs =>
              if Nat.eqb (List.length ps) (List.length vs) then
                fst (List.fold_left
                       (fun (acc : match_result value * list value) (p : Ast.pat Tannot.t) =>
                          let '(r, vs) := acc in
                          match vs with
                          | [] => (Unmatched, [])
                          | v :: rest => (r ⋈ pattern_match p v, rest)
                          end)
                       ps (simple_match value, vs))
              else
                Unmatched
          | _ => simple_match value
          end
      | Ast.P_app ctor ps =>
          match v with
          | V_ctor m =>
              match m !! Aux.unwrap ctor with
              | None => Unmatched
              | Some vs =>
                  if Nat.eqb (List.length ps) (List.length vs) then
                    let inner :=
                      fst (List.fold_left
                             (fun (acc : match_result value * list value) (p : Ast.pat Tannot.t) =>
                                let '(r, vs) := acc in
                                match vs with
                                | [] => (Unmatched, [])
                                | v :: rest => (r ⋈ pattern_match p v, rest)
                                end)
                             ps (simple_match value, vs))
                    in
                    (* If [v] could be other constructors too, demote a Matched
                       result to MaybeMatched (the bindings are still right,
                       but the residual evaluator should still consider the
                       other arms). *)
                    if Nat.eqb (size m) 1 then inner
                    else match inner with
                         | Matched b => MaybeMatched b
                         | other => other
                         end
              else
                Unmatched
              end
          | V_top => simple_match value
          | _ => Unmatched
          end
      | Ast.P_struct _ field_pats _ =>
          match v with
          | V_record m =>
              List.fold_left
                (fun (acc : match_result value) (fp : Ast.id * Ast.pat Tannot.t) =>
                  let '(field, fpat) := fp in
                  match m !! Aux.unwrap field with
                  | None => Unmatched
                  | Some fv => acc ⋈ pattern_match fpat fv
                  end)
                field_pats (simple_match value)
          | V_top => simple_match value
          | _ => Unmatched
          end
      | Ast.P_vector_concat ps =>
          match v with
          | V_bitvector bv =>
              (* Sail's view of a bitvector is MSB-first: in [P_vector_concat
                 [p1; p2; p3]], [p1] matches the high bits and [p3] the low
                 bits. We don't know the total length up-front so we trust
                 the splits in each pattern's typing annotation and walk left
                 to right, keeping an [offset] (in LSB-based bits from the
                 low end) that decreases as we go. *)
              let total :=
                List.fold_left
                  (fun (acc : nat) p =>
                    let 'Ast.P_aux _ ann := p in
                    match Tannot.get_split (snd ann) with
                    | TypeAnnot.Types.Split n => Nat.add acc n
                    | TypeAnnot.Types.No_split => acc
                    end)
                  ps 0%nat
              in
              fst (List.fold_left
                     (fun (acc : match_result value * nat) (p : Ast.pat Tannot.t) =>
                       let '(prev, off) := acc in
                       let 'Ast.P_aux _ ann := p in
                       match Tannot.get_split (snd ann) with
                       | TypeAnnot.Types.Split s =>
                           let off' := Nat.sub off s in
                           let piece :=
                             V_bitvector (Dbv.slice bv (N.of_nat off') (N.of_nat s))
                           in
                           (prev ⋈ pattern_match p piece, off')
                       | TypeAnnot.Types.No_split => (Unmatched, off)
                       end)
                     ps (simple_match value, total))
          | V_top => simple_match value
          | _ => Unmatched
          end
      | Ast.P_list ps =>
          (* [[||]] / [[|x|]] / [[|x, y|]] — the pattern is a concrete list
             literal that matches a list of exactly the same length. *)
          match v with
          | V_list vs =>
              if Nat.eqb (List.length ps) (List.length vs) then
                fst (List.fold_left
                       (fun (acc : match_result value * list value) (p : Ast.pat Tannot.t) =>
                          let '(r, vs) := acc in
                          match vs with
                          | [] => (Unmatched, [])
                          | v :: rest => (r ⋈ pattern_match p v, rest)
                          end)
                       ps (simple_match value, vs))
              else
                Unmatched
          | V_top => simple_match value
          | _ => Unmatched
          end
      | Ast.P_cons head_pat tail_pat =>
          (* [h :: t] matches a non-empty list, binding [head_pat] to the head
             and [tail_pat] to the tail. *)
          match v with
          | V_list (h :: t) =>
              pattern_match head_pat h ⋈ pattern_match tail_pat (V_list t)
          | V_list [] => Unmatched
          | V_top => simple_match value
          | _ => Unmatched
          end
      | Ast.P_vector_subrange id n m =>
          (* [v[n..m]] records a partial binding for [v]: this match has
             consumed the slice [v[n..m]], which the surrounding
             [P_vector_concat] (or the standalone use) has already cut out
             of the matched value. [complete_partial] later reassembles
             all partial bindings for [v] into a single bitvector. *)
          add_match id (Partial (Ast.Non_empty (v, n, m) [])) (simple_match value)
      | Ast.P_vector ps =>
          (* A single-element-per-bit vector pattern. For a [V_bitvector] of
             length [n = List.length ps], the leftmost (MSB-first) pattern
             matches the highest bit and the rightmost matches bit 0. *)
          match v with
          | V_bitvector bv =>
              let n := List.length ps in
              fst (List.fold_left
                     (fun (acc : match_result value * nat) (p : Ast.pat Tannot.t) =>
                       let '(prev, off) := acc in
                       let off' := Nat.sub off 1 in
                       let piece :=
                         V_bitvector (Dbv.slice bv (N.of_nat off') (N.of_nat 1))
                       in
                       (prev ⋈ pattern_match p piece, off'))
                     ps (simple_match value, n))
          | V_vector vs =>
              if Nat.eqb (List.length ps) (List.length vs) then
                fst (List.fold_left
                       (fun (acc : match_result value * list value) (p : Ast.pat Tannot.t) =>
                         let '(prev, vs) := acc in
                         match vs with
                         | [] => (Unmatched, [])
                         | v :: rest => (prev ⋈ pattern_match p v, rest)
                         end)
                       ps (simple_match value, vs))
              else Unmatched
          | V_top => simple_match value
          | _ => Unmatched
          end
      | _ => simple_match value
      end.
  End Matching.

  (** Read the sub-value at place [p] within the root variable's value
      [v], used to rebuild the intermediate levels of a nested update.
      Reads degrade to [V_top]: an absent field or unknown element just
      means uninitialised storage, so a freshly-written nested field
      still produces a recognisable nested value. *)
  Fixpoint read_place (p : place value) (v : value) : value :=
    match p with
    | PL_id _ _ => v
    | PL_register _ => v
    | PL_field p' fld => get_field (read_place p' v) (Aux.unwrap fld)
    | PL_vector p' n =>
        match concrete_int n with
        | Some i => get_vector_elem (read_place p' v) i
        | None => V_top
        end
    | PL_vector_range _ _ _ => V_top
    end.

  (** <<update_place p x v>> updates the value [v], by replacing the
      subvalue at [p] with [x]. A vector index or range bound we can't
      pin down to a concrete integer leaves [v] unchanged — the caller's
      residual still records the write. *)
  Fixpoint update_place (p : place value) (x : value) (v : value) : value :=
    match p with
    | PL_id _ _ => x
    | PL_register _ => x
    | PL_field p' fld =>
        update_place p' (set_field (read_place p' v) (Aux.unwrap fld) x) v
    | PL_vector p' n =>
        match concrete_int n with
        | Some i => update_place p' (set_vector_elem (read_place p' v) i x) v
        | None => v
        end
    | PL_vector_range p' hi lo =>
        match concrete_int hi, concrete_int lo with
        | Some h, Some l => update_place p' (set_bv_range (read_place p' v) h l x) v
        | _, _ => v
        end
    end.

  (** Split the assigned value [v] across the places of a destructuring
      assignment. Tuple targets walk a known [V_tuple] in lockstep;
      bitvector concatenation targets slice a known-width [V_bitvector]
      by each sub-target's width (the leftmost sub-target gets the high
      bits, following [Order dec]). Whenever we can't split — unknown
      value shape, unknown width — we return no updates for the
      remaining places, leaving those variables' state unchanged. *)
  Fixpoint destructure_assignment (d : destructure value) (v : value) : list (place value * value) :=
    match d with
    | DL_place p => [(p, v)]
    | DL_tuple ds =>
        match v with
        | V_tuple vs =>
            (fix go (ds : list (destructure value)) (vs : list value) : list (place value * value) :=
               match ds, vs with
               | d :: ds', v :: vs' => destructure_assignment d v ++ go ds' vs'
               | _, _ => []
               end) ds vs
        | _ => []
        end
    | DL_vector_concat sds =>
        match concrete_bv_length v with
        | Some total =>
            (fix go (sds : list (TypeAnnot.Types.vector_concat_split * destructure value)) (cur_hi : Z) : list (place value * value) :=
               match sds with
               | [] => []
               | (TypeAnnot.Types.Split w, d) :: rest =>
                   let wz := Z.of_nat w in
                   let lo := (cur_hi + 1 - wz)%Z in
                   destructure_assignment d (bv_slice v (Z.to_N lo) (N.of_nat w)) ++ go rest (cur_hi - wz)%Z
               | (TypeAnnot.Types.No_split, _) :: _ => []
               end) sds (total - 1)%Z
        | None => []
        end
    end.

  Fixpoint place_root (p : place value) : option Ast.id :=
    match p with
    | PL_id id _ => Some id
    | PL_register r =>
        option_map (fun reg_id => Ast.Id_aux reg_id Ast.ext_unknown_loc) (concrete_ref r)
    | PL_vector p' _ => place_root p'
    | PL_vector_range p' _ _ => place_root p'
    | PL_field p' _ => place_root p'
    end.

  (** Reassemble the slices recorded by a [Partial] binding (one entry
      per [v[hi..lo]] sub-pattern) into a single [V_bitvector]. We assume
      the slices' bit ranges together cover [0..max], which is the only
      shape Sail's typechecker actually produces — for [v[3..0] @ v[7..4]]
      we get [{(_, 3, 0); (_, 7, 4)}] and reassemble an 8-bit value. *)
  Definition complete_partial (partial_values : Ast.non_empty (t * Z * Z)) : t :=
    let 'Ast.Non_empty (v1, n1, m1) rest := partial_values in
    let '(max, _) :=
      List.fold_left
        (fun (range : Z * Z) (pvalue : t * Z * Z) =>
         let '(max, min) := range in
         let '(_, n, m) := pvalue in
         (Z.max max (Z.max n m), Z.min min (Z.min n m)))
        rest (Z.max n1 m1, Z.min n1 m1)
    in
    let len := Z.succ max in
    let zeros :=
      V_bitvector (Dbv.α (Bit.Bits.to_bvn (List.repeat Bit.B0 (Z.to_nat len))))
    in
    List.fold_left
      (fun bv pvalue =>
       let '(slice, n, m) := pvalue in
       set_bv_range bv (Z.max n m) (Z.min n m) slice)
      ((v1, n1, m1) :: rest)
      zeros.

  Definition complete (b : PatternMatch.binding t) : t :=
    match b with
    | PatternMatch.Complete v => v
    | PatternMatch.Partial vs => complete_partial vs
    end.
End Dom.
