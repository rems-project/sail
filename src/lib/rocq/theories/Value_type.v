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
From Stdlib Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import OrderedType.
From Stdlib Require Import RelationClasses.

Require Import Ast.
Require Import AstInduction.
Require Import Bit.
Require Import IdUtil.
Require Import ListUtil.

Import ListNotations.

Declare Scope Value_scope.
Delimit Scope Value_scope with value.

(* A value is fully defined if it contains no unknown values *)
Fixpoint fully_defined (v : value) : bool :=
  match v with
  | V_vector vs | V_list vs | V_ctor _ vs | V_tuple vs => forallb fully_defined vs
  | V_record fields => forallb (fun '(_, v) => fully_defined v) fields
  | V_unknown => false
  | _ => true
  end.

(* Induction rule for values, needed as they contain nested lists of values *)
Section value_ind.
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
            (H_unknown : P V_unknown).

  Fixpoint value_ind v : P v.
  Proof using All.
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
    - apply H_unknown.
  Qed.
End value_ind.

Fixpoint value_cmp (f : value -> bool) (lhs rhs : value) : bool :=
  match (lhs, rhs) with
  | (V_bitvector l_bv, V_bitvector r_bv) => list_eqb bit_eqb l_bv r_bv
  | (V_vector l_v, V_vector r_v) => list_eqb (value_cmp f) l_v r_v
  | (V_list l_xs, V_list r_ys) => list_eqb (value_cmp f) l_xs r_ys
  | (V_int l, V_int r) => (l =? r)%Z
  | (V_real l, V_real r) => QArith_base.Qeq_bool l r
  | (V_bool l, V_bool r) => Bool.eqb l r
  | (V_tuple l_v, V_tuple r_v) => list_eqb (value_cmp f) l_v r_v
  | (V_unit, V_unit) => true
  | (V_string l, V_string r) => (l =? r)%string
  | (V_ref l, V_ref r) => id_eqb l r
  | (V_member l, V_member r) => id_eqb l r
  | (V_ctor l_id l_v, V_ctor r_id r_v) => id_eqb l_id r_id && list_eqb (value_cmp f) l_v r_v
  | (V_record l_fields, V_record r_fields) =>
      list_eqb (fun '(l_id, l_v) '(r_id, r_v) => id_eqb l_id r_id && value_cmp f l_v r_v) l_fields r_fields
  | (v, V_unknown) => f v
  | _ => false
  end.

Definition is_unknown (v : value) : bool :=
  match v with
  | V_unknown => true
  | _ => false
  end.

Definition value_eqb (lhs rhs : value) : bool := value_cmp is_unknown lhs rhs.
Definition value_leb (lhs rhs : value) : bool := value_cmp (fun _ => true) lhs rhs.

Infix "=?" := value_eqb (at level 70, no associativity) : Value_scope.
Infix "<=?" := value_leb (at level 70, no associativity) : Value_scope.

Definition value_ltb (lhs rhs : value) : bool := (lhs <=? rhs)%value && negb (lhs =? rhs)%value.

Infix "<?" := value_ltb (at level 70, no associativity) : Value_scope.

Create HintDb sail.

Hint Immediate id_eqb_refl : sail.
Hint Immediate bit_eqb_refl : sail.
Hint Immediate Z.eqb_refl : sail.
Hint Immediate Qeq_bool_refl : sail.
Hint Immediate eqb_reflx : sail.
Hint Immediate String.eqb_refl : sail.
Hint Resolve list_eqb_refl : sail.
Hint Resolve Forall_cons_iff : sail.

Lemma value_cmp_refl : forall f v, f V_unknown = true -> value_cmp f v v = true.
Proof.
  intros f v U.
  induction v using value_ind.
  (* Solve all the trivial non-recursive cases *)
  all: try (unfold value_cmp; solve [auto with sail]).
  (* Handle any cases where the value just contains a list of other values *)
  all: try (
    change (list_eqb (value_cmp f) vs vs = true);
    induction vs as [| v vs];
    match goal with
    | |- list_eqb (value_cmp _) [] [] = true => reflexivity
    | _ =>
        apply Forall_cons_iff in H;
        destruct H as (H1 & H2);
        cbn;
        rewrite H1;
        rewrite IHvs;
        reflexivity || apply H2
    end
  ).
  - induction vs as [| v vs].
    + change (id_eqb id id && true = true).
      solve [auto with sail bool].
    + apply Forall_cons_iff in H.
      destruct H as (H1 & H2).
      change (id_eqb id id && (value_cmp f v v && list_eqb (value_cmp f) vs vs) = true).
      rewrite H1.
      change (Forall (fun v : value => value_cmp f v v = true) vs ->
              id_eqb id id && list_eqb (value_cmp f) vs vs = true) in IHvs.
      auto with sail bool.
  - induction fields as [| fld flds].
    + reflexivity.
    + apply Forall_cons_iff in H.
      destruct H as (H1 & H2).
      destruct fld as [id v].
      change (id_eqb id id &&
              value_cmp f v v &&
              list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_cmp f l_v r_v)) flds flds = true).
      auto with sail bool.
Qed.

Lemma value_eqb_refl : forall v, (v =? v)%value = true.
Proof.
  intros.
  unfold value_eqb.
  apply (value_cmp_refl is_unknown).
  cbn.
  reflexivity.
Qed.

Lemma value_leb_refl : forall v, (v <=? v)%value = true.
Proof.
  intros.
  unfold value_leb.
  apply value_cmp_refl.
  reflexivity.
Qed.

Lemma value_ltb_not_eqb : forall x y, (x <? y)%value = true -> (x =? y)%value = false.
Proof.
  intros x y x_ltb_y.
  unfold value_ltb in x_ltb_y.
  rewrite andb_true_iff, negb_true_iff in x_ltb_y.
  tauto.
Qed.

Lemma value_eqb_comm : forall v1 v2, (v1 =? v2)%value = (v2 =? v1)%value.
Proof.
  intros v1.
  induction v1 using value_ind.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm.
    intros x y; destruct x; destruct y; reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (Forall_in _ _ _ H H1).
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (Forall_in _ _ _ H H1).
  - destruct v2; try reflexivity.
    cbn.
    apply Z.eqb_sym.
  - destruct v2; try reflexivity.
    cbn.
    apply Qeq_bool_comm.
  - destruct v2; try reflexivity.
    cbn.
    destruct b; destruct b0; reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (Forall_in _ _ _ H H1).
  - destruct v2; try reflexivity.
  - destruct v2; try reflexivity.
    cbn.
    apply String.eqb_sym.
  - destruct v2; try reflexivity.
    unfold value_eqb.
    destruct id as [x_aux ?].
    destruct i as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
  - destruct v2; try reflexivity.
    unfold value_eqb.
    destruct id as [x_aux ?].
    destruct i as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    change (id_eqb id id0 && list_eqb value_eqb vs vs0 = id_eqb id0 id && list_eqb value_eqb vs0 vs).
    assert (id_eqb id id0 = id_eqb id0 id).
    destruct id as [x_aux ?].
    destruct id0 as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
    rewrite H1.
    assert (list_eqb value_eqb vs vs0 = list_eqb value_eqb vs0 vs).
    cbn.
    apply list_eqb_comm_in.
    intros.
    destruct vs.
    cbn in H1.
    easy.
    apply (Forall_in _ _ _ H H2).
    rewrite H2.
    reflexivity.
  - intros v2.
    induction v2 using value_ind; try reflexivity.
    change (list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) fields fields0 =
            list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) fields0 fields).
    apply list_eqb_comm_in.
    intros.
    destruct fields.
    cbn in H1.
    easy.
    destruct x.
    destruct y.
    assert (id_eqb i i0 = id_eqb i0 i).
    destruct i as [x_aux ?].
    destruct i0 as [y_aux ?].
    destruct x_aux as [| | x_s | x_s]; destruct y_aux as [| | y_s | y_s]; cbn; try trivial; rewrite String.eqb_sym; easy.
    rewrite H2.
    destruct p.
    assert (value_eqb v v0 = value_eqb v0 v).
    apply Forall_cons_iff in H.
    destruct H.
    cbn in H.
    cbn in H1.
    destruct H1.
    rewrite pair_equal_spec in H1.
    destruct H1.
    rewrite H4 in H.
    apply H.
    apply (Forall_in _ _ _ H3 H1 v0).
    rewrite H3.
    reflexivity.
  - intros v2.
    destruct v2; trivial.
Qed.

Lemma value_cmp_ctor : forall f lid lvs rid rvs, value_cmp f (V_ctor lid lvs) (V_ctor rid rvs) = true <-> (id_eqb lid rid = true /\ list_eqb (value_cmp f) lvs rvs = true).
Proof.
  split; cbn in *; rewrite andb_true_iff in *; easy.
Qed.

Lemma value_cmp_trans : forall f x y z (F : (forall x, f x = true) \/ f = is_unknown \/ (forall x, x <> V_unknown -> f x = true)),
  value_cmp f x y = true ->
  value_cmp f y z = true ->
  value_cmp f x z = true.
Proof.
  intros f x y z F.
  revert x z.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ]; try easy.
  all: intro z; destruct z as [ zbv | zs | zs | zi | zr | zb | zs | | zstr | zid | zid | zid zs | zfields | ]; try easy.
  all: intros L R.
  all: try (
    unfold value_cmp in *;
    destruct F as [LE | [EQ | LT]];
    match goal with
    | [ LT : (forall (x : value), x <> V_unknown -> ?f x = true) |- ?f ?V = true ] => apply (LT V); discriminate
    | [ LE : (forall (x : value), ?f x = true) |- ?f ?V = true ] => apply (LE V)
    | [ EQ : ?f = is_unknown |- _ ] => rewrite EQ in *; cbn in *; assumption
    end
  ).
  - cbn in *.
    apply (fun P => list_eqb_trans _ bit_eqb xbv ybv zbv P L R).
    intros x y z; destruct x; destruct y; destruct z; easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (Forall_in _ _ _ H In_y); easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (Forall_in _ _ _ H In_y); easy.
  - cbn in *.
    rewrite Z.eqb_eq in *.
    apply (eq_trans L R).
  - cbn in *.
    apply (Qeq_bool_trans _ _ _ L R).
  - cbn in *.
    rewrite eqb_true_iff in *.
    apply (eq_trans L R).
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (Forall_in _ _ _ H In_y); easy.
  - cbn in *.
    rewrite String.eqb_eq in *.
    apply (eq_trans L R).
  - apply (id_eqb_trans _ _ _ L R).
  - apply (id_eqb_trans _ _ _ L R).
  - rewrite value_cmp_ctor in *.
    destruct L as (Lid & Ll).
    destruct R as (Rid & Rl).
    split.
    + apply (id_eqb_trans _ yid _); assumption.
    + apply (list_eqb_trans_in _ _ _ ys _); try assumption.
      intros x y z In_y XY YZ.
      apply (Forall_in _ _ _ H In_y); easy.
  - apply (list_eqb_trans_in _ _ _ yfields _); try assumption.
    intros x y z In_y XY YZ.
    destruct x as [xid xv].
    destruct y as [yid yv].
    destruct z as [zid zv].
    rewrite andb_true_iff in *.
    destruct XY as (XY1 & XY2).
    destruct YZ as (YZ1 & YZ2).
    split.
    + apply (id_eqb_trans _ yid _); assumption.
    + apply (Forall_in _ (yid, yv) yfields H In_y); assumption.
Qed.

Lemma value_eqb_trans : forall x y z, (x =? y)%value = true -> (y =? z)%value = true -> (x =? z)%value = true.
Proof.
  intros x y z.
  apply value_cmp_trans.
  auto.
Qed.

Lemma value_leb_trans : forall x y z, (x <=? y)%value = true -> (y <=? z)%value = true -> (x <=? z)%value = true.
Proof.
  intros x y z.
  apply value_cmp_trans.
  auto.
Qed.

Lemma value_eqb_leb : forall x y, (x =? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y.
  revert x.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | ys | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xs | ]; try easy.
  all: unfold value_leb, value_eqb; cbn iota delta - [id_eqb] zeta; try easy.
  all:
    revert H; revert xs;
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy;
    lazymatch goal with
    | x : _ * _, y : _ * _ |- _ => destruct x; destruct y
    | _ => idtac
    end;
    cbn iota delta - [id_eqb] zeta;
    repeat rewrite andb_true_iff;
    repeat split;
    lazymatch goal with
    | |- id_eqb _ _ = true => tauto
    | |- list_eqb _ _ _ = true =>
        assert (IH := IHys xs (Forall_inv_tail H));
        repeat rewrite andb_true_iff in IH;
        tauto
    | |- value_cmp _ _ _ = true =>
        apply (Forall_inv H); unfold value_eqb; tauto
    end.
Qed.

Lemma value_ltb_leb : forall x y, (x <? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y H.
  unfold value_ltb in H.
  rewrite andb_true_iff in H.
  tauto.
Qed.

Lemma value_ltb_is_leb : forall x y, (x <? y)%value = true -> (x <=? y)%value = true.
Proof.
  intros x y.
  revert x.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ]; try easy.
  all: unfold value_ltb; cbn beta delta - [id_eqb] iota; rewrite andb_true_iff; easy.
Qed.

Lemma value_ltb_trans_h : forall x y z, (x <=? y)%value = true -> (y <? z)%value = true -> (x =? z)%value = false.
Proof.
  intros x y z.
  revert x z.
  induction y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | ys | ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xs | ]; try easy.
  all: intro z; destruct z as [ zbv | zs | zs | zi | zr | zb | zs | | zstr | zid | zid | zid zs | zs | ]; try easy.
  all: intros L R.
  (* Solve all the non-recursive cases *)
  all: try (unfold value_ltb in R; cbn in R; rewrite andb_negb_r in R; discriminate).
  all: try (
    unfold value_ltb in R;
    rewrite andb_true_iff, negb_true_iff in R;
    destruct R as (Rleb & Rneqb);
    cbn iota beta delta - [id_eqb] in Rleb, Rneqb, L;
    lazymatch goal with
    | Rleb : _ && _ = true |- _ => rewrite andb_true_iff in Rleb; destruct Rleb as (yz_id & Rleb)
    | _ => idtac
    end;
    lazymatch goal with
    | L : _ && _ = true |- _ => rewrite andb_true_iff in L; destruct L as (xy_id & L)
    | _ => idtac
    end;
    lazymatch goal with
    | Rneqb : _ && _ = false |- _ =>
        rewrite andb_false_iff in Rneqb;
        destruct Rneqb as [yz_id_neq | Rneqb];
        [> rewrite yz_id in yz_id_neq; easy | idtac]
    | _ => idtac
    end;
    assert (ys_zs_length := list_eqb_same_length _ _ _ Rleb);
    rewrite -> (list_eqb_false _ _ _ ys_zs_length) in Rneqb;
    apply Exists_exists in Rneqb;
    destruct Rneqb as [pair H0];
    destruct pair as (v_y, v_z);
    destruct H0;
    apply in_app_split in H0;
    destruct H0 as [yzs1 H0];
    destruct H0 as [yzs2 H0];
    rewrite (zip_fst_snd _ _ _ ys_zs_length) in H0;
    repeat rewrite map_app in H0;
    cbn in H0;
    destruct H0;
    cbn iota beta delta - [id_eqb];
    match goal with
    | |- id_eqb _ _ && _ = false => rewrite andb_false_iff; apply or_intror
    | _ => idtac
    end;
    rewrite H2;
    apply list_eqb_false_app_r;
    remember (drop (Datatypes.length (map snd yzs1)) xs) as xstl;
    destruct xstl; [reflexivity | idtac];
    cbn;
    apply andb_false_intro1;
    apply (Forall_in _ v_y _ H (app_cons_in _ _ _ _ H0)); [
      assert (xs_ys_length := list_eqb_same_length _ _ _ L);
      assert (xs_zs_length := list_eqb_same_length _ _ _ Rleb);
      unfold value_leb;
      rewrite (take_app_drop (length (map snd yzs1)) xs), H0 in L;
      apply list_eqb_app in L; [
        rewrite <- Heqxstl in L;
        cbn in L;
        apply andb_true_iff in L;
        tauto
      | repeat rewrite length_map;
        rewrite take_length; [ reflexivity | idtac ];
        rewrite xs_ys_length, H0, length_app, length_map;
        apply Nat.le_add_r
      ]
    | idtac
    ];
    unfold value_ltb, value_leb, value_eqb;
    cbn in Rleb;
    rewrite H0, H2 in Rleb;
    apply list_eqb_app in Rleb;
    [
      cbn in Rleb;
      apply andb_true_iff in Rleb;
      apply andb_true_iff;
      split; [ tauto | rewrite negb_true_iff; assumption ]
    | repeat rewrite length_map;
      reflexivity
    ]
  ).
  -
    unfold value_ltb in R;
    rewrite andb_true_iff, negb_true_iff in R;
    destruct R as (Rleb & Rneqb);
    cbn iota beta delta - [id_eqb] in Rleb, Rneqb, L;
    lazymatch goal with
    | Rleb : _ && _ = true |- _ => rewrite andb_true_iff in Rleb; destruct Rleb as (yz_id & Rleb)
    | _ => idtac
    end;
    lazymatch goal with
    | L : _ && _ = true |- _ => rewrite andb_true_iff in L; destruct L as (xy_id & L)
    | _ => idtac
    end;
    lazymatch goal with
    | Rneqb : _ && _ = false |- _ =>
        rewrite andb_false_iff in Rneqb;
        destruct Rneqb as [yz_id_neq | Rneqb];
        [> rewrite yz_id in yz_id_neq; easy | idtac]
    | _ => idtac
    end.
    assert (ys_zs_length := list_eqb_same_length _ _ _ Rleb);
    rewrite -> (list_eqb_false _ _ _ ys_zs_length) in Rneqb;
    apply Exists_exists in Rneqb;
    destruct Rneqb as [pair H0];
    destruct pair as (v_y, v_z).
    lazymatch goal with
    | v_y : _ * _, v_z : _ * _ |- _ =>
      remember v_y as V;
      destruct v_y as (f_y, v_y'); destruct v_z as (f_z, v_z)
    | _ => idtac
    end.
    destruct H0;
    apply in_app_split in H0;
    destruct H0 as [yzs1 H0];
    destruct H0 as [yzs2 H0];
    rewrite (zip_fst_snd _ _ _ ys_zs_length) in H0;
    repeat rewrite map_app in H0;
    cbn in H0;
    destruct H0.
    cbn iota beta delta - [id_eqb].
    lazymatch goal with
    | |- id_eqb _ _ && _ = false => rewrite andb_false_iff; apply or_intror
    | _ => idtac
    end.
    rewrite H2;
    apply list_eqb_false_app_r;
    remember (drop (Datatypes.length (map snd yzs1)) xs) as xstl.
    destruct xstl as [| h_xstl t_xstl]; [reflexivity | idtac].
    lazymatch goal with
    | h_xstl : _ * _ |- _ => destruct h_xstl
    | _ => idtac
    end.
    cbn iota beta delta - [id_eqb] zeta.
    apply andb_false_intro1.
    apply andb_false_intro2.
    apply (Forall_in _ V _ H (app_cons_in _ _ _ _ H0)); rewrite HeqV.
    + assert (xs_ys_length := list_eqb_same_length _ _ _ L);
      assert (xs_zs_length := list_eqb_same_length _ _ _ Rleb).
      unfold value_leb;
      rewrite (take_app_drop (length (map snd yzs1)) xs), H0 in L.
      apply list_eqb_app in L.
      *
        rewrite <- Heqxstl in L.
        cbn iota beta delta - [id_eqb] zeta in L.
        rewrite HeqV in L, H1.
        repeat rewrite andb_true_iff in L.
        cbn.
        tauto.
      * repeat rewrite length_map;
        rewrite take_length; [ reflexivity | idtac ];
        rewrite xs_ys_length, H0, length_app, length_map;
        apply Nat.le_add_r.
    + unfold value_ltb, value_leb, value_eqb;
      cbn iota beta delta - [id_eqb] zeta in Rleb.
      rewrite H0, H2 in Rleb.
      apply list_eqb_app in Rleb.
      * cbn iota beta delta - [id_eqb] zeta in Rleb.
        rewrite HeqV in H1, Rleb.
        repeat rewrite andb_true_iff in Rleb;
        apply andb_true_iff.
        split.
        **
          cbn.
          tauto.
        **
          rewrite negb_true_iff; cbn.
          rewrite andb_false_iff in H1.
          destruct H1.
          *** rewrite H1 in Rleb. easy.
          *** assumption.
      * repeat rewrite length_map.
        reflexivity.
Qed.

Lemma value_ltb_trans : forall x y z, (x <? y)%value = true -> (y <? z)%value = true -> (x <? z)%value = true.
Proof.
  intros x y z XY YZ.
  apply value_ltb_leb in XY.
  unfold value_ltb.
  rewrite andb_true_iff, negb_true_iff.
  split.
  - apply (value_leb_trans _ y _ XY (value_ltb_leb _ _ YZ)).
  - apply (value_ltb_trans_h _ y _ XY YZ).
Qed.

Lemma value_leb_antisym : forall x y, (x <=? y)%value = true -> (y <=? x)%value = true -> (x =? y)%value = true.
Proof.
  intros x.
  induction x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields | ] using value_ind.
  all: intros y.
  all: destruct y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields | ]; try easy.
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (Forall_in _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (Forall_in _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - revert H. revert xs.
    induction ys as [ | y ys]; intros xs H; destruct xs as [| x xs]; try easy.
    intros X_le_Y Y_le_X.
    cbn in *.
    rewrite andb_true_iff in *.
    destruct X_le_Y as (x_le_y & xs_le_ys).
    destruct Y_le_X as (y_le_x & ys_le_xs).
    split.
    + unfold value_eqb, value_leb in H.
      apply (Forall_in _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
    + apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - cbn beta delta - [id_eqb] iota.
    repeat rewrite andb_true_iff.
    intros X_le_Y Y_le_X.
    split.
    + easy.
    + destruct X_le_Y as (_ & xs_le_ys).
      destruct Y_le_X as (_ & ys_le_xs).
      revert H xs_le_ys ys_le_xs. revert xs.
      induction ys as [| y ys]; intros xs H; destruct xs as [|x xs]; try easy.
      intros X_le_Y Y_le_X.
      cbn in *.
      rewrite andb_true_iff in *.
      destruct X_le_Y as (x_le_y & xs_le_ys).
      destruct Y_le_X as (y_le_x & ys_le_xs).
      split.
      * unfold value_eqb, value_leb in H.
        apply (Forall_in _ x (x :: xs) H (in_eq _ _) y x_le_y y_le_x).
      * apply (IHys xs (Forall_inv_tail H) xs_le_ys ys_le_xs).
  - cbn beta delta - [id_eqb] iota.
    revert H. revert xfields.
    induction yfields as [| y yfields]; intros xfields H; destruct xfields as [| x xfields]; try easy.
    intros X_le_Y Y_le_X.
    cbn beta delta - [id_eqb] iota in *.
    destruct x as (x_id, x_v).
    destruct y as (y_id, y_v).
    repeat rewrite andb_true_iff in *.
    destruct X_le_Y as (X_le_Y & xs_le_ys).
    destruct Y_le_X as (Y_le_X & ys_le_xs).
    split; try split; try easy.
    + destruct X_le_Y as (_ & x_le_y).
      destruct Y_le_X as (_ & y_le_x).
      unfold value_eqb, value_leb in H.
      apply (Forall_in _ (x_id, x_v) (_ :: xfields) H (in_eq _ _) _ x_le_y y_le_x).
    + apply (IHyfields _ (Forall_inv_tail H) xs_le_ys ys_le_xs).
Qed.

Module Order.
  Definition eq (x y : value) : Prop := Is_true (value_eqb x y).

  Definition le (x y : value) : Prop := Is_true (value_leb x y).

  Instance eq_Equivalence : Equivalence eq.
  Proof.
    split.
    - intro x.
      unfold eq.
      apply Is_true_eq_left.
      apply (value_eqb_refl x).
    - intros x y H.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H.
      rewrite (value_eqb_comm y x).
      assumption.
    - intros x y z H1 H2.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H1.
      apply Is_true_eq_true in H2.
      apply (value_eqb_trans x y z H1 H2).
  Qed.

  Instance le_PreOrder : PreOrder le.
  Proof.
    split.
    - intro x.
      unfold eq.
      apply Is_true_eq_left.
      apply (value_leb_refl x).
    - intros x y z H1 H2.
      unfold eq in *.
      apply Is_true_eq_left.
      apply Is_true_eq_true in H1.
      apply Is_true_eq_true in H2.
      apply (value_leb_trans x y z H1 H2).
  Qed.

  Instance le_Antisymmetric : Antisymmetric value eq le.
  Proof.
    intros x y XY YX.
    apply Is_true_eq_left.
    apply Is_true_eq_true in XY.
    apply Is_true_eq_true in YX.
    apply (value_leb_antisym _ _ XY YX).
  Qed.

  Instance le_PartialOrder : PartialOrder eq le.
  Proof.
    intros x y.
    cbn.
    unfold flip.
    split.
    - intros H.
      apply Is_true_eq_true in H.
      unfold eq, le in *.
      split.
      + apply Is_true_eq_left.
        apply (value_eqb_leb _ _ H).
      + apply Is_true_eq_left.
        rewrite value_eqb_comm in H.
        apply (value_eqb_leb _ _ H).
    - intros H.
      apply antisymmetry; tauto.
  Qed.
End Order.

Module Primops.
  Definition gt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.gtb v1 v2))
    | _ => None
    end.

  Definition lt_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_bool (Z.ltb v1 v2))
    | _ => None
    end.

  Definition add_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.add v1 v2))
    | _ => None
    end.

  Definition sub_int (v1 : value) (v2 : value) : option value :=
    match (v1, v2) with
    | (V_int v1, V_int v2) => Some (V_int (Z.sub v1 v2))
    | _ => None
    end.

  Definition zero_extend (bits : value) (n : value) : option value :=
    match (bits, n) with
    | (V_bitvector bitlist, V_int n) =>
      let len := List.length bitlist in
      if Z.ltb n (Z.of_nat len) then
        None
      else
        let extend := Nat.sub (Z.to_nat n) len in
        Some (V_bitvector (List.repeat B0 extend ++ bitlist))
    | _ => None
    end.
End Primops.
