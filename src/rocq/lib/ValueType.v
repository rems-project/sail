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

From Sail Require Import Ast.
From Sail Require Import AstInduction.
From Sail Require Import Bit.
From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import Tactics.
From Sail Require BitList.

Import ListNotations.

Declare Scope Value_scope.
Delimit Scope Value_scope with value.

Definition value_of_lit (lit : Ast.lit) : value :=
  let 'L_aux aux _ := lit in
  match aux with
  | L_unit => V_unit
  | L_true => V_bool true
  | L_false => V_bool false
  | L_num n => V_int n
  | L_hex h => V_bitvector (BitList.of_hex_lit h)
  | L_bin b => V_bitvector (BitList.of_bin_lit b)
  | L_real r => V_real r
  | L_string s => V_string s
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
            (H_record : forall fields, Forall (fun f => P (snd f)) fields -> P (V_record fields)).

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
  Qed.
End value_ind.

Fixpoint value_eqb (lhs rhs : value) : bool :=
  match (lhs, rhs) with
  | (V_bitvector l_bv, V_bitvector r_bv) => list_eqb bit_eqb l_bv r_bv
  | (V_vector l_v, V_vector r_v) => list_eqb value_eqb l_v r_v
  | (V_list l_xs, V_list r_ys) => list_eqb value_eqb l_xs r_ys
  | (V_int l, V_int r) => (l =? r)%Z
  | (V_real l, V_real r) => QArith_base.Qeq_bool l r
  | (V_bool l, V_bool r) => Bool.eqb l r
  | (V_tuple l_v, V_tuple r_v) => list_eqb value_eqb l_v r_v
  | (V_unit, V_unit) => true
  | (V_string l, V_string r) => (l =? r)%string
  | (V_ref l, V_ref r) => id_eqb l r
  | (V_member l, V_member r) => id_eqb l r
  | (V_ctor l_id l_v, V_ctor r_id r_v) => id_eqb l_id r_id && list_eqb value_eqb l_v r_v
  | (V_record l_fields, V_record r_fields) =>
      list_eqb (fun '(l_id, l_v) '(r_id, r_v) => id_eqb l_id r_id && value_eqb l_v r_v) l_fields r_fields
  | _ => false
  end.

Infix "=?" := value_eqb (at level 70, no associativity) : Value_scope.

Create HintDb sail.

Hint Immediate id_eqb_refl : sail.
Hint Immediate bit_eqb_refl : sail.
Hint Immediate Z.eqb_refl : sail.
Hint Immediate Qeq_bool_refl : sail.
Hint Immediate eqb_reflx : sail.
Hint Immediate String.eqb_refl : sail.
Hint Resolve list_eqb_refl : sail.
Hint Resolve Forall_cons_iff : sail.

Lemma value_eqb_refl : forall v, (v =? v)%value = true.
Proof.
  intros v.
  induction v using value_ind.
  (* Solve all the trivial non-recursive cases *)
  all: try (unfold value_eqb; solve [auto with sail]).
  (* Handle any cases where the value just contains a list of other values *)
  all: try (
    change (list_eqb value_eqb vs vs = true);
    induction vs as [| v vs];
    match goal with
    | |- list_eqb value_eqb [] [] = true => reflexivity
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
      change (id_eqb id id && (value_eqb v v && list_eqb value_eqb vs vs) = true).
      rewrite H1.
      change (Forall (fun v : value => value_eqb v v = true) vs ->
              id_eqb id id && list_eqb value_eqb vs vs = true) in IHvs.
      auto with sail bool.
  - induction fields as [| fld flds].
    + reflexivity.
    + apply Forall_cons_iff in H.
      destruct H as (H1 & H2).
      destruct fld as [id v].
      change (id_eqb id id &&
              value_eqb v v &&
              list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) flds flds = true).
      auto with sail bool.
Qed.

Lemma value_eqb_comm : forall v1 v2, (v1 =? v2)%value = (v2 =? v1)%value.
Proof.
  intros x;
  induction x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields ] using value_ind;
  intros y; destruct y as [ ybv | ys | ys | yi | yr | yb | ys | | ystr | yid | yid | yid ys | yfields ]; try reflexivity.
  all: try (
    reintros xs IH ys;
    cbn;
    apply list_eqb_comm_in;
    intros ?? In;
    apply (Forall_in _ _ _ IH In)
  ).
  - cbn; apply (list_eqb_comm _ _ _ _ (@Bit.bit_eqb_comm)).
  - apply Z.eqb_sym.
  - apply Qeq_bool_comm.
  - cbn; destruct xb; destruct yb; reflexivity.
  - apply String.eqb_sym.
  - apply id_eqb_comm.
  - apply id_eqb_comm.
  - reintros xid xs IH yid ys.
    change (id_eqb xid yid && list_eqb value_eqb xs ys = id_eqb yid xid && list_eqb value_eqb ys xs).
    f_equal.
    + apply id_eqb_comm.
    + apply list_eqb_comm_in.
      intros ?? In;
      apply (Forall_in _ _ _ IH In).
  - reintros xfields IH yfields.
    change (list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) xfields yfields =
            list_eqb (fun '(l_id, l_v) '(r_id, r_v) => andb (id_eqb l_id r_id) (value_eqb l_v r_v)) yfields xfields).
    apply list_eqb_comm_in.
    intros xfld yfld In.
    destruct xfld as (xf, xv).
    destruct yfld as (yf, yv).
    f_equal.
    + apply id_eqb_comm.
    + assert (H := Forall_in _ _ _ IH In).
      apply H.
Qed.

Lemma value_cmp_ctor : forall lid lvs rid rvs, value_eqb (V_ctor lid lvs) (V_ctor rid rvs) = true <-> (id_eqb lid rid = true /\ list_eqb value_eqb lvs rvs = true).
Proof.
  split; cbn in *; rewrite andb_true_iff in *; easy.
Qed.

Lemma value_eqb_trans : forall x y z, (x =? y)%value = true -> (y =? z)%value = true -> (x =? z)%value = true.
Proof.
  intros x y z.
  revert x z.
  induction y as [ ybv | ys IH | ys IH | yi | yr | yb | ys IH | | ystr | yid | yid | yid ys IH | yfields IH ] using value_ind.
  all: intro x; destruct x as [ xbv | xs | xs | xi | xr | xb | xs | | xstr | xid | xid | xid xs | xfields ]; try easy.
  all: intro z; destruct z as [ zbv | zs | zs | zi | zr | zb | zs | | zstr | zid | zid | zid zs | zfields ]; try easy.
  all: intros L R.
  - cbn in *.
    apply (fun P => list_eqb_trans _ bit_eqb xbv ybv zbv P L R).
    intros x y z; destruct x, y, z; easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (Forall_in _ _ _ IH In_y); easy.
  - cbn in *.
    apply (fun P => list_eqb_trans_in _ _ xs ys zs P L R).
    intros x y z In_y XY YZ.
    apply (Forall_in _ _ _ IH In_y); easy.
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
    apply (Forall_in _ _ _ IH In_y); easy.
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
      apply (Forall_in _ _ _ IH In_y); easy.
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
    + apply (Forall_in _ (yid, yv) yfields IH In_y); assumption.
Qed.

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
