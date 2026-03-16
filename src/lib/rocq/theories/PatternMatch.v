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

Require Import Tactics.
Require Import Ast.
Require Import AstInduction.
Require Import Bit.
Require Import IdUtil.
Require Import ListUtil.
Require Import ValueType.

Require BitList.
Require TypeAnnot.

Import ListNotations.

(**
A [binding] is something an identifier in a pattern can bind with
during matching. The [Complete] case is for the regular case where an
identifier is just bound to a [value]. The [Partial] case is for Sail
vector range patterns, e.g.

<<
  match xs : bits(32) with
  | ys[15 .. 0] @ ys[31 .. 16] => ...
>>

After pattern matching is complete, these partial bindings are
turned into a complete binding for the << ys >> variable. See the
[complete_bindings] function later in this module.
*)

Inductive binding (V : Set) :=
| Complete : value -> binding V
| Partial : non_empty (V * Z * Z) -> binding V.

Arguments Complete {_}.
Arguments Partial {_}.

(** Now we define an equality predicate [binding_eqb] for the [binding] type. *)

Definition binding_part_eqb (l r : value * Z * Z) :=
  let '(lv, ln, lm) := l in
  let '(rv, rn, rm) := r in
  value_eqb lv rv && (ln =? rn)%Z && (lm =? rm)%Z.

Definition binding_eqb (l r : binding value) : bool :=
  match (l, r) with
  | (Complete lv, Complete rv) => value_eqb lv rv
  | (Partial (Non_empty lv lvs), Partial (Non_empty rv rvs)) =>
      binding_part_eqb lv rv && list_eqb binding_part_eqb lvs rvs
  | _ => false
  end.

Lemma binding_part_eqb_refl : forall p, binding_part_eqb p p = true.
Proof.
  intros p.
  destruct p as (vn, m).
  destruct vn as (v, n).
  cbn.
  repeat (apply andb_true_intro; split).
  - apply value_eqb_refl.
  - apply Z.eqb_refl.
  - apply Z.eqb_refl.
Qed.

Lemma binding_eqb_refl : forall b, binding_eqb b b = true.
Proof.
  intros b.
  destruct b as [b | p].
  - cbn; apply value_eqb_refl.
  - destruct p as [part parts].
    cbn.
    apply andb_true_intro; split.
    + apply binding_part_eqb_refl.
    + apply list_eqb_refl; intros; apply binding_part_eqb_refl.
Qed.

(**
Now we define a notion of combining two bindings. Consider a tuple pattern.

<<
  (pat1, pat2)
>>

The Sail type system will ensure subpatterns like pat1 and pat2 do
not bind the same identifiers, so either we will have no binding
for an identifier in << pat1 >> [None] or it will have [Some]
binding for a variable. The only special case is for the vector
range patterns above, where we combine the partial matches.
*)

Definition combine_binding {V} (l r : option (binding V)) : option (binding V) :=
  match (l, r) with
  | (None, None) => None
  | (Some b, None) => Some b
  | (None, Some b) => Some b
  | (Some lb, Some rb) =>
      match (lb, rb) with
      | (Complete v, _) => Some (Complete v)
      | (_, Complete v) => Some (Complete v)
      | (Partial (Non_empty lv lvs), Partial (Non_empty rv rvs)) =>
          Some (Partial (Non_empty lv (lvs ++ rv :: rvs)))
      end
  end.

Lemma combine_binding_none_left : forall {V} (b : option (binding V)), combine_binding None b = b.
Proof.
  intros ? b; destruct b; cbn; reflexivity.
Qed.

Lemma combine_binding_none_right : forall {V} (b : option (binding V)), combine_binding b None = b.
Proof.
  intros ? b; destruct b; cbn; reflexivity.
Qed.

Lemma combine_binding_assoc : forall {V} (a b c : option (binding V)), combine_binding (combine_binding a b) c = combine_binding a (combine_binding b c).
Proof.
  intros ? a b c.
  (destruct a as [a |]; [destruct a | idtac]);
  (destruct b as [b |]; [destruct b | idtac]);
  (destruct c as [c |]; [destruct c | idtac]).
  all: cbn; try reflexivity.
  all: repeat (
    match goal with
    | [ n : non_empty _ |- _ ] => destruct n; cbn; try reflexivity
    end
  ).
  rewrite app_comm_cons.
  rewrite app_assoc.
  reflexivity.
Qed.

(**
We now lift [combine_binding] to the sets of identifiers being
bound by different subpatterns using [IdMap.map2].
*)

Definition merge_bindings {V} (l r : IdMap.t (binding V)) : IdMap.t (binding V) :=
  IdMap.map2 combine_binding l r.

Definition unwrap_default {A : Set} (default : A) (opt : option A) : A :=
  match opt with
  | None => default
  | Some x => x
  end.

Lemma merge_bindings_in_left : forall {V k} {x y : IdMap.t (binding V)},
  IdMap.In k x -> IdMap.In k (merge_bindings x y).
Proof.
  intros ? k x y H.
  pose proof H as H_in.
  change (exists e, IdMap.MapsTo k e x) in H.
  destruct H as [b H].
  change (exists e, IdMap.MapsTo k e (merge_bindings x y)).
  exists (unwrap_default b (combine_binding (Some b) (IdMap.find k y))).
  apply IdMap.find_2.
  unfold merge_bindings.
  rewrite IdMap.map2_1.
  - apply IdMap.find_1 in H.
    rewrite H.
    case_eq (IdMap.find k y).
    + intro b'.
      destruct b as [? | n]; cbn; try tauto.
      destruct n.
      destruct b' as [? | n']; cbn; try tauto.
      destruct n'; cbn; tauto.
    + cbn; tauto.
  - tauto.
Qed.

Lemma merge_bindings_in_right : forall {V k} {y x : IdMap.t (binding V)}, IdMap.In k y -> IdMap.In k (merge_bindings x y).
Proof.
  intros ? k y x H.
  pose proof H as H_in.
  change (exists e, IdMap.MapsTo k e y) in H.
  destruct H as [b H].
  change (exists e, IdMap.MapsTo k e (merge_bindings x y)).
  exists (unwrap_default b (combine_binding (IdMap.find k x) (Some b))).
  apply IdMap.find_2.
  unfold merge_bindings.
  rewrite IdMap.map2_1.
  - apply IdMap.find_1 in H.
    rewrite H.
    case_eq (IdMap.find k x).
    + intro b'.
      destruct b' as [? | n']; cbn; try tauto.
      destruct n'; cbn; try tauto.
      destruct b as [? | n]; cbn; try tauto.
      destruct n; cbn; tauto.
    + cbn; tauto.
  - tauto.
Qed.

Lemma merge_bindings_in_iff : forall {V k} {x y : IdMap.t (binding V)}, IdMap.In k (merge_bindings x y) <-> IdMap.In k x \/ IdMap.In k y.
Proof.
  intros ? k x y.
  split; intros H.
  - unfold merge_bindings.
    apply (IdMap.map2_2 H).
  - destruct H as [Hx | Hy].
    + apply (merge_bindings_in_left Hx).
    + apply (merge_bindings_in_right Hy).
Qed.

Lemma not_in_map2 : forall A k (x y : IdMap.t A) f, ~ IdMap.In k x -> ~ IdMap.In k y -> ~ IdMap.In (elt:=A) k (IdMap.map2 f x y).
Proof.
  intros A k x y f Not_in_x Not_in_y.
  unfold not.
  intros In_xy.
  apply IdMap.map2_2 in In_xy.
  tauto.
Qed.

Lemma not_in_find_none : forall [A k] (x : IdMap.t A), ~ IdMap.In k x <-> IdMap.find k x = None.
Proof.
  intros A k x.
  split; intros H.
  - change (~ (exists m, IdMap.MapsTo k m x)) in H.
    unfold not in H.
    case_eq (IdMap.find k x).
    + intros elt Find_x.
      exfalso.
      apply IdMap.find_2 in Find_x.
      destruct H.
      exists elt.
      assumption.
    + tauto.
  - unfold not.
    intros In_x.
    change (exists elt, IdMap.MapsTo k elt x) in In_x.
    destruct In_x as [elt In_x].
    apply IdMap.find_1 in In_x.
    rewrite In_x in H.
    discriminate H.
Qed.

Lemma map2_none_none : forall [A k] (x y : IdMap.t A) f,
  IdMap.find k x = None ->
  IdMap.find k y = None ->
  IdMap.find (elt:=A) k (IdMap.map2 f x y) = None.
Proof.
  intros A k x y f.
  repeat rewrite <- not_in_find_none.
  intros X Y.
  apply not_in_map2; assumption.
Qed.

(**
We now define some simple tactics to help prove associativity of merging bindings.

First, Define a simple tactic that attempts to simplify hypothesis that involve [IdMap.find].
*)

Ltac idmap_find_simp_step :=
  lazymatch goal with
  | [ H : context [ IdMap.find ?k (IdMap.map2 combine_binding ?x ?y) ], X : IdMap.find ?k ?x = None, Y : IdMap.find ?k ?y = None |- _ ] =>
      rewrite (map2_none_none x y combine_binding X Y) in H
  | [ H : context [ IdMap.find ?k ?x ], X : IdMap.find ?k ?x = None |- _ ] =>
      rewrite X in H
  | [ H : context [ IdMap.find ?k ?x ], X : IdMap.find ?k ?x = Some ?b |- _ ] =>
      rewrite X in H
  | [ H : context [ combine_binding (combine_binding ?x ?y) ?z ] |- _ ] =>
      rewrite combine_binding_assoc in H
  end.

Ltac idmap_find_simp := repeat idmap_find_simp_step.

(**
Second, Define a tactic idmap_in_solve that attempts to solve goals of the form [IdMap.In _ _].
*)

Ltac idmap_in_step :=
  lazymatch goal with
  | |- IdMap.In ?k (IdMap.map2 combine_binding ?x ?y) => change (IdMap.In k (merge_bindings x y))
  | [ H : IdMap.find ?k ?x = Some _ |- IdMap.In ?k (merge_bindings ?x ?y) ] => apply merge_bindings_in_left
  | [ H : IdMap.find ?k ?y = Some _ |- IdMap.In ?k (merge_bindings ?x ?y) ] => apply merge_bindings_in_right

  | [ H : IdMap.find ?k ?x = None |- IdMap.In ?k ?x \/ IdMap.In ?k _ ] => apply or_intror
  | [ H : IdMap.find ?k ?y = None |- IdMap.In ?k _ \/ IdMap.In ?k ?y ] => apply or_introl
  | [ H : IdMap.find ?k ?x = Some _ |- IdMap.In ?k ?x \/ IdMap.In ?k _ ] => apply or_introl
  | [ H : IdMap.find ?k ?y = Some _ |- IdMap.In ?k _ \/ IdMap.In ?k ?y ] => apply or_intror

  | [ H : IdMap.find ?k ?x = Some ?b |- IdMap.In ?k ?x ] =>
      change (exists b, IdMap.MapsTo k b x);
      exists b;
      apply (IdMap.find_2 H)
  end.

Ltac idmap_in_solve := solve [ repeat idmap_in_step ].

(**
Third, Define a tactic binding_eqb_solve that attempts to solve goals of the form [binding_eqb b1 b2 = true].
*)

Ltac binding_eqb_solve_step :=
  match goal with
  | [ H1 : ?x = Some ?b1, H2 : ?x = Some ?b2 |- binding_eqb ?b1 ?b2 = true ] =>
      let Eq := fresh "Eq" in
      rewrite H1 in H2;
      injection H2;
      intros Eq;
      rewrite Eq;
      apply binding_eqb_refl
  | [ H1 : ?x = Some ?b1, H2 : ?y = Some ?b2 |- binding_eqb ?b1 ?b2 = true ] =>
      let Eq := fresh "Eq" in
      assert (x = y) as Eq; [
        cbn; reflexivity
      | rewrite Eq in H1
      ]
  end.

Ltac binding_eqb_solve := solve [ repeat binding_eqb_solve_step ].

(**
Merging binding maps is associative.
*)

Lemma merge_bindings_assoc : forall x y z,
  IdMap.Equivb binding_eqb (merge_bindings (merge_bindings x y) z) (merge_bindings x (merge_bindings y z)).
Proof.
  intros x y z.
  split.

  - intro k.
    change (IdMap.In k (merge_bindings (merge_bindings x y) z) <-> IdMap.In k (merge_bindings x (merge_bindings y z))).
    repeat rewrite merge_bindings_in_iff.
    rewrite or_assoc.
    reflexivity.

  (* If M is the merge bindings function, we must prove:
     `(k, M x (M y z)) ↦ e` and `(k, M (M x y) z) ↦ e' then `binding_eqb e e' = true`. *)
  - intros k b b' L R.
    change (IdMap.MapsTo k b (merge_bindings (merge_bindings x y) z)) in L.
    change (IdMap.MapsTo k b' (merge_bindings x (merge_bindings y z))) in R.

    (* Remember a hypothesis H that k is in the merged bindings *)
    assert (exists b, IdMap.MapsTo k b (merge_bindings (merge_bindings x y) z)) as H by eauto.
    change (IdMap.In k (merge_bindings (merge_bindings x y) z)) in H.
    repeat rewrite merge_bindings_in_iff in H.
    apply IdMap.find_1 in L, R.
    unfold merge_bindings in L, R.

    (case_eq (IdMap.find k x); [ intros xb Find_x | intros None_x]);
    (case_eq (IdMap.find k y); [ intros yb Find_y | intros None_y]);
    (case_eq (IdMap.find k z); [ intros zb Find_z | intros None_z]).

    (* First handle the case where k is none of the maps.
       This is impossible due to the hypothesis H we created. *)
    8: {
      destruct H as [H | In_z]; [ destruct H as [In_x | In_y] | idtac ].
      all: (
        match goal with
        | [ In : IdMap.In ?k ?x, None : IdMap.find ?k ?x = None |- _ ] =>
            change (exists b, IdMap.MapsTo k b x) in In;
            destruct In as [b'' In];
            apply IdMap.find_1 in In;
            rewrite In in None;
            discriminate None
        end
      ).
    }

    all: (
      repeat (rewrite IdMap.map2_1 in L; [ idtac | idmap_in_solve ]; idmap_find_simp);
      repeat (rewrite IdMap.map2_1 in R; [ idtac | idmap_in_solve ]; idmap_find_simp);
      binding_eqb_solve
    ).
Qed.

Definition update_list (xs : list bit) (n : nat) (y : bit) : list bit :=
  let n := List.length xs - n - 1 in
  let '(ys, zs) := take_drop n xs in
  ys ++ [y] ++ List.tl zs.

Fixpoint update_subrange (xs : list bit) (n : nat) (ys : list bit) : list bit :=
  match ys with
  | [] => xs
  | y :: ys =>
    update_subrange (update_list xs n y) (n - 1) ys
  end.

Definition complete_value (partial_values : non_empty (value * Z * Z)) : value :=
  let '(Non_empty (v1, n1, m1) partial_values) := partial_values in
    let '(max, min) :=
      List.fold_left
        (fun range pvalue =>
         let '(max, min) := range in
         let '(_, n, m) := pvalue in
         (Z.max max (Z.max n m), Z.min min (Z.min n m)))
        partial_values (n1, m1)
    in
    let len := Z.sub (Z.succ max) min in
    let zeros := List.repeat B0 (Z.to_nat len) in
    let value :=
      List.fold_left
        (fun bv pvalue =>
         let '(slice, n, _) := pvalue in
         match slice with
         | V_bitvector slice => update_subrange bv (Z.to_nat n) slice
         | _ => bv
         end)
        ((v1, n1, m1) :: partial_values)
        zeros
    in
    V_bitvector value.

Definition complete_bindings (m : IdMap.t (binding value)) : IdMap.t value :=
  IdMap.map
    (fun b =>
       match b with
       | Complete v => v
       | Partial vs => complete_value vs
       end
    )
    m.

Inductive match_result {V : Set} : Type :=
| Matched : IdMap.t (binding V) -> match_result
| MaybeMatched : IdMap.t (binding V) -> match_result
| Unmatched : match_result.

Arguments match_result V : clear implicits.

Definition match_result_eq (l r : match_result value) : Prop :=
  match (l, r) with
  | (Unmatched, Unmatched) => True
  | (Matched l_b, Matched r_b) => IdMap.Equivb binding_eqb l_b r_b
  | (MaybeMatched l_b, MaybeMatched r_b) => IdMap.Equivb binding_eqb l_b r_b
  | _ => False
  end.

Definition merge_match_result (l r : match_result value) : match_result value :=
  match (l, r) with
  | (Unmatched, _) => Unmatched
  | (_, Unmatched) => Unmatched
  | (MaybeMatched l_b, MaybeMatched r_b) => MaybeMatched (merge_bindings l_b r_b)
  | (Matched l_b,      MaybeMatched r_b) => MaybeMatched (merge_bindings l_b r_b)
  | (MaybeMatched l_b, Matched r_b     ) => MaybeMatched (merge_bindings l_b r_b)
  | (Matched l_b,      Matched r_b     ) => Matched (merge_bindings l_b r_b)
  end.

Infix "⋈" := merge_match_result (right associativity, at level 60).

Lemma merge_match_result_assoc : forall a b c, match_result_eq ((a ⋈ b) ⋈ c) (a ⋈ (b ⋈ c)).
Proof.
  intros a b c.
  destruct a as [a | a |]; destruct b as [b | b |]; destruct c as [c | c |].
  all: cbn; try reflexivity; apply merge_bindings_assoc.
Qed.

Definition empty_bindings : IdMap.t (binding value) := @IdMap.empty (binding value).

Definition simple_match : match_result value := Matched empty_bindings.

Definition simple_match_when (b : bool) : match_result value :=
  if b then simple_match else Unmatched.

Definition add_match (k : id) (v : binding value) (r : match_result value) : match_result value :=
  match r with
  | Unmatched => Unmatched
  | MaybeMatched b => MaybeMatched (IdMap.add k v b)
  | Matched b => Matched (IdMap.add k v b)
  end.

Definition fully_matched (r : match_result value) : Prop :=
  match r with
  | MaybeMatched _ => False
  | _ => True
  end.

Definition neg_match (r : match_result value) : match_result value :=
  match r with
  | Unmatched => simple_match
  | MaybeMatched b => MaybeMatched b
  | Matched _ => Unmatched
  end.

Definition or_match (l r : match_result value) : match_result value :=
  match (l, r) with
  | (Matched l_b, _) => Matched l_b
  | (_, Matched r_b) => Matched r_b
  | (MaybeMatched l_b, _) => MaybeMatched l_b
  | (_, MaybeMatched r_b) => MaybeMatched r_b
  | _ => Unmatched
  end.

Fixpoint binds_id {A} (n : Ast.id) (p : Ast.pat A) : bool :=
  let 'P_aux aux annot := p in
  match aux with
  | P_lit _ | P_wild | P_not _ => false
  | P_id m => id_eqb n m
  | P_typ _ p | P_var p _ => binds_id n p
  | P_as pat m => binds_id n pat || id_eqb n m
  | P_tuple ps | P_list ps | P_vector ps | P_app _ ps | P_vector_concat ps | P_string_append ps =>
      fold_left orb (map (binds_id n) ps) false
  | P_or p1 p2 | P_cons p1 p2 => binds_id n p1 || binds_id n p2
  | P_struct _ ps _ => fold_left orb (map (fun fp => binds_id n (snd fp)) ps) false
  | P_vector_subrange m _ _ => id_eqb n m
  end.


Definition pattern_match_literal (l : Ast.lit) (v : value) : match_result value :=
  let 'L_aux aux annot := l in
  match (aux, v) with
  | (L_unit,      V_unit        ) => simple_match
  | (L_true,      V_bool true   ) => simple_match
  | (L_false,     V_bool false  ) => simple_match
  | (L_num n,     V_int m       ) => simple_match_when (Z.eqb n m)
  | (L_hex s,     V_bitvector vs) => simple_match_when (BitList.same_bits (BitList.of_hex_lit s) vs)
  | (L_bin s,     V_bitvector vs) => simple_match_when (BitList.same_bits (BitList.of_bin_lit s) vs)
  | (L_string s1, V_string s2   ) => simple_match_when (String.eqb s1 s2)
  | (L_real r1,   V_real r2     ) => simple_match_when (QArith_base.Qeq_bool r1 r2)
  | (_,           V_unknown     ) => MaybeMatched empty_bindings
  | _ => Unmatched
  end.

Fixpoint get_struct_field (name : id) (fields : list (id * value)) {struct fields} : value :=
  match fields with
  | (name', v) :: rest_fields =>
      if id_eqb name name' then
        v
      else
        get_struct_field name rest_fields
  | [] => V_unit
  end.

Module Make (Tannot : TypeAnnot.S).

  Fixpoint fold_match
      (f : pat Tannot.t -> value -> match_result value)
      (ps : list (pat Tannot.t))
      (match_info : match_result value * list value)
      : match_result value * list value :=
    match ps with
    | [] => match_info
    | p :: ps =>
        let match_info :=
          match match_info with
          | (_, []) => (Unmatched, [])
          | (prev, v :: vs) => (prev ⋈ f p v, vs)
          end
        in
        fold_match f ps match_info
    end.

  Fixpoint pattern_match (p : Ast.pat Tannot.t) (v : value) {struct p} : match_result value :=
    let 'P_aux aux annot := p in
    match aux with
    | P_wild => simple_match
    | P_id n =>
        match Tannot.get_id_type (snd annot) n with
        | Enum_member =>
            match v with
            | V_member m => simple_match_when (id_eqb n m)
            | V_unknown  => MaybeMatched empty_bindings
            | _          => Unmatched
            end
        | _ => Matched (IdMap.add n (Complete v) empty_bindings)
        end
    | P_typ _ p => pattern_match p v
    | P_lit l => pattern_match_literal l v
    | P_as p n => add_match n (Complete v) (pattern_match p v)
    | P_app ctor ps =>
        match v with
        | V_ctor v_ctor vs =>
            if id_eqb ctor v_ctor then fst (fold_match pattern_match ps (simple_match, vs)) else Unmatched
        | _ => Unmatched
        end
    | P_tuple [] =>
        match v with
        | V_unit | V_unknown => simple_match
        | _ => Unmatched
        end
    | P_tuple ps =>
        match v with
        | V_tuple vs =>
            fst (fold_match pattern_match ps (simple_match, vs))
        | _ => Unmatched
        end
    | P_list ps =>
        match v with
        | V_list vs =>
            if Nat.eqb (List.length ps) (List.length vs) then
              fst (fold_match pattern_match ps (simple_match, vs))
            else
              Unmatched
        | _ => Unmatched
        end
    | P_vector ps =>
        match BitList.to_gvector v with
        | V_vector vs => fst (fold_match pattern_match ps (simple_match, vs))
        | _ => Unmatched
        end
    | P_vector_concat ps =>
        match v with
        | V_bitvector bs =>
            fst (fold_left
                   (fun match_info p =>
                    let '(P_aux _ annot) := p in
                    match Tannot.get_split (snd annot) with
                    | Split s =>
                        match match_info with
                        | (_, []) => (Unmatched, [])
                        | (prev, bs) =>
                            let '(bs_take, bs_drop) := take_drop s bs in
                            (prev ⋈ pattern_match p (V_bitvector bs_take), bs_drop)
                        end
                    | No_split => (Unmatched, [])
                    end)
                   ps
                   (simple_match, bs))
        | V_vector vs =>
            fst (fold_left
                   (fun match_info p =>
                    let '(P_aux _ annot) := p in
                    match Tannot.get_split (snd annot) with
                    | Split s =>
                        match match_info with
                        | (_, []) => (Unmatched, [])
                        | (prev, vs) =>
                            let '(vs_take, vs_drop) := take_drop s vs in
                            (prev ⋈ pattern_match p (V_vector vs_take), vs_drop)
                        end
                    | No_split => (Unmatched, [])
                    end)
                   ps
                   (simple_match, vs))
        | _ => Unmatched
        end
    | P_cons p ps =>
        match v with
        | V_list (v :: vs) => pattern_match p v ⋈ pattern_match ps (V_list vs)
        | _ => Unmatched
        end
    | P_or lhs_p rhs_p => or_match (pattern_match lhs_p v) (pattern_match rhs_p v)
    | P_not p => neg_match (pattern_match p v)
    | P_var p _ => pattern_match p v
    | P_struct _ field_patterns _ =>
        match v with
        | V_record fields =>
            fold_left
              (fun prev fp =>
                 let '(name, p) := fp in
                 let v := get_struct_field name fields in
                 prev ⋈ pattern_match p v
              )
              field_patterns
              simple_match
        | _ => Unmatched
        end
    | P_vector_subrange id n m => Matched (IdMap.add id (Partial (Non_empty (v, n, m) [])) empty_bindings)
    (* TODO *)
    | P_string_append _ => simple_match
    end.

  Lemma fm_fold_unmatched : forall pats vs,
    fully_matched (fst (fold_match pattern_match pats (Unmatched, vs))).
  Proof.
    intros pats.
    induction pats as [| pat pats IH]; intros vs.
    - reflexivity.
    - destruct vs; apply IH.
  Qed.

  Lemma fm_fold_matched : forall pats vs b,
    Forall (fun v => fully_defined v = true) vs ->
    Forall
      (fun p => forall v, fully_defined v = true -> fully_matched (pattern_match p v))
      pats ->
    fully_matched (fst (fold_match pattern_match pats (Matched b, vs))).
  Proof.
    intros pats.
    induction pats as [| pat pats IH]; intros vs b FD_vs H.
    - reflexivity.
    - destruct vs as [| v vs]; cbn.
      + apply fm_fold_unmatched.
      + rewrite Forall_cons_iff in H, FD_vs.
        destruct H as [H_hd H_tl].
        destruct FD_vs as [FD_vs_hd FD_vs_tl].
        apply H_hd in FD_vs_hd.
        case_eq (pattern_match pat v).
        * intros ? Match_pat.
          apply (IH _ _ FD_vs_tl H_tl).
        * intros ? MaybeMatched_pat.
          exfalso.
          rewrite MaybeMatched_pat in FD_vs_hd.
          cbn in FD_vs_hd.
          apply FD_vs_hd.
        * intros Unmatched_pat.
          apply fm_fold_unmatched.
  Qed.

  Definition MatcherResult {A} (xs : list A) (m : match_result value * list A) : Prop :=
    fully_matched (fst m) /\ Suffix (snd m) xs.

  Lemma fm_fold_left_matched : forall [A B] (pats : list B) (matcher : (match_result value * list A) -> B -> (match_result value * list A)) vs m,
    Forall
      (fun p =>
        forall m vs', fully_matched m -> Suffix vs' vs -> MatcherResult vs' (matcher (m, vs') p))
      pats ->
    fully_matched m ->
    fully_matched (fst (fold_left matcher pats (m, vs))).
  Proof.
    intros A B pats matcher.
    induction pats as [| pat pats IH]; intros vs m H Init.
    - apply Init.
    - cbn.
      rewrite Forall_cons_iff in H.
      destruct H as [H_hd H_tl].

      specialize (H_hd m vs Init (Suffix_refl vs)).

      destruct (matcher (m, vs) pat) as (m', vs') eqn : Matcher_hd.
      destruct H_hd as [FM_m' Drop_vs].
      cbn in Drop_vs, FM_m'.
      destruct Drop_vs as [i]; subst.

      destruct m' as [b' | b' |].
      + apply (IH (drop i vs) (Matched b')).
        * apply (fun G => Forall_impl _ G H_tl).
          intros pat' Q m'' vs' FM_m'' Drop_vs'.
          destruct Drop_vs' as [j]; subst.

          specialize (fun G => Q m'' (drop j (drop i vs)) G).
          assert (L : exists n : nat, drop j (drop i vs) = drop n vs).
          {
             exists (i + j).
             apply drop_drop_add.
          }
          apply (Q FM_m'' L).
        * reflexivity.
      + exfalso.
        apply FM_m'.
      + apply (IH (drop i vs) Unmatched).
        * apply (fun G => Forall_impl _ G H_tl).
          intros pat' Q m'' vs' FM_m'' Drop_vs'.
          destruct Drop_vs' as [j]; subst.

          specialize (fun G => Q m'' (drop j (drop i vs)) G).
          assert (L : exists n : nat, drop j (drop i vs) = drop n vs).
          {
             exists (i + j).
             apply drop_drop_add.
          }
          apply (Q FM_m'' L).
        * reflexivity.
  Qed.

  Ltac fm_simp :=
    lazymatch goal with
    | |- fully_matched (Matched _) => reflexivity
    | |- fully_matched (MaybeMatched _) => exfalso
    | |- fully_matched Unmatched => reflexivity

    | |- fully_matched simple_match => unfold simple_match; reflexivity
    | |- fully_matched (add_match _ _ _) => unfold add_match; fm_simp
    | |- fully_matched (neg_match _) => unfold neg_match; fm_simp
    | |- fully_matched (simple_match_when _) => unfold simple_match_when; fm_simp
    | |- fully_matched (if ?b then _ else _) => destruct b; fm_simp

    | |- fully_matched (fst (fold_match pattern_match _ (simple_match, _))) =>
        apply (fm_fold_matched _ _ empty_bindings)

    | |- fully_matched (fst (fold_left ?matcher ?pats (?m, ?vs))) =>
        apply (fm_fold_left_matched pats matcher vs m); fm_simp

    | |- fully_matched (match pattern_match ?p ?v with | Matched _ => _ | MaybeMatched _ => _ | Unmatched => _ end) =>
        case_eq (pattern_match p v); intros; fm_simp

    | |- fully_matched (fst (_, _)) => unfold fst; fm_simp

    | |- fully_matched (match ?v with _ => _ end) =>
        let T := type of v in
        let LD := fresh "LD" in
        lazymatch T with
        | value => destruct v eqn : LD; fm_simp
        | id_type => destruct v; fm_simp
        | list _ => destruct v eqn : LD; fm_simp
        | _ => destruct v eqn : LD; fm_simp
        end

    | |- fully_matched (fst (match ?v with _ => _ end)) =>
        let T := type of v in
        let LD := fresh "LD" in
        lazymatch T with
        | value => destruct v eqn : LD; fm_simp
        | id_type => destruct v; fm_simp
        | list _ => destruct v eqn : LD; fm_simp
        | _ => destruct v eqn : LD; fm_simp
        end

    | |- _ => idtac
    end.

  Ltac solve_fd_once tac :=
    lazymatch goal with
    | [ IH : (forall v : value, fully_defined v = true -> fully_matched (pattern_match ?p v)),
        H : fully_defined ?v = true,
        M : pattern_match ?p ?v = MaybeMatched _
      |- _
      ] => exfalso; apply IH in H; rewrite M in H; cbn in H; assumption

    | [ IH : (forall v : value, fully_defined v = true -> fully_matched (pattern_match ?p v)),
        H : fully_defined ?v = true
      |- fully_matched (pattern_match ?p ?v) ] =>
        apply IH; apply H

    | [ H1 : pattern_match ?p ?v = MaybeMatched _, H2 : fully_matched (pattern_match ?p ?v) |- _ ] =>
        destruct (pattern_match p v); (discriminate + tauto)

    | _ => tac
    end.

  Ltac solve_fd := solve_fd_once easy.

  Lemma fully_defined_match_literal : forall lit v, fully_defined v = true -> fully_matched (pattern_match_literal lit v).
  Proof.
    intros lit v H.
    destruct lit as [aux ?].
    destruct aux; destruct v; try reflexivity; cbn; fm_simp; easy.
  Qed.

  Lemma fully_defined_struct_field : forall i flds,
    forallb (fun fld => fully_defined (snd fld)) flds = true ->
    fully_defined (get_struct_field i flds) = true.
  Proof.
    intros i flds H.
    induction flds as [| fld flds IH].
    - reflexivity.
    - cbn beta delta - [id_eqb] iota.
      destruct fld as (field_name, v).
      cbn in H.
      rewrite andb_true_iff in H.
      destruct H as [H_hd H_tl].
      destruct (id_eqb i field_name).
      + tauto.
      + exact (IH H_tl).
  Qed.

  Lemma struct_fdm_helper : forall field_patterns fields m,
     fold_left (fun prev fp =>
        let '(name, p) := fp in
        let v := get_struct_field name fields in
        prev ⋈ pattern_match p v
      ) field_patterns m
    =
      fst (
        fold_left (fun '(prev, fields) fp =>
            let '(name, p) := fp in
            let v := get_struct_field name fields in
            (prev ⋈ pattern_match p v, fields)
          )
          field_patterns
          (m, fields)
      ).
  Proof.
    intros field_patterns fields.
    induction field_patterns as [| fp fps IH]; intros m.
    - reflexivity.
    - cbn beta delta - [merge_match_result] iota.
      rewrite IH.
      destruct fp.
      reflexivity.
  Qed.

  Lemma fully_defined_match : forall p v, fully_defined v = true -> fully_matched (pattern_match p v).
  Proof.
    intros p.
    induction p using pat_ind_g; intros v FD.
    all: try (cbn; reflexivity).
    all: try (cbn beta delta - [id_eqb] iota; fm_simp; solve_fd).
    - apply (fully_defined_match_literal _ _ FD).
    - cbn beta delta - [id_eqb] iota.
      fm_simp; try assumption.
      cbn in FD.
      rewrite forallb_forall in FD.
      rewrite Forall_forall.
      assumption.
    - reintros IH v FD.
      cbn beta delta - [id_eqb] iota.
      fm_simp; try assumption.
      reintros vec G.
      destruct v; cbn in G; inversion G.
      + (* Bitvector *)
        reintros Is_bitvector.
        rewrite Forall_forall.
        intros ? In.
        rewrite in_map_iff in In.
        destruct In as [bit In].
        destruct In as [B _].
        rewrite <- B.
        reflexivity.
      + (* Generic vector *)
        reintros Is_vector.
        rewrite Forall_forall.
        intros ? In.
        cbn in FD.
        rewrite forallb_forall in FD.
        rewrite <- Is_vector in In.
        exact (FD _ In).
    - reintros IH v FD.
      cbn beta delta - [id_eqb] iota.
      fm_simp; apply (fun P => Forall_impl _ P IH).
      + (* Bitvector *)
        reintros bits _ FD.
        intros pat Q m bits' FD_m Drop.
        destruct pat as [pat_aux ?].
        unfold MatcherResult; split.
        * fm_simp; try apply FD_m.
          reintros t d TD i P.
          specialize (Q (V_bitvector t)).
          cbn beta delta - [pattern_match] iota in Q.
          specialize (Q (eq_refl true)).
          destruct (pattern_match (P_aux pat_aux _) (V_bitvector t)); (discriminate + apply Q).
        * destruct_match; cbn; try suffix_solve.
      + (* Generic vector *)
        reintros vec _ FD.
        intros pat Q m ? FD_m Drop.
        destruct pat as [pat_aux ?].
        unfold MatcherResult; split.
        * fm_simp; try apply FD_m.
          reintros t ? TD ? ?.
          specialize (Q (V_vector t)).
          cbn beta delta - [pattern_match] iota in FD, Q.
          assert (L : forallb fully_defined t = true).
          {
            rewrite take_drop_split in TD.
            inversion TD.
            apply forallb_take.
            apply (Suffix_forallb Drop).
            exact FD.
          }
          apply Q in L.
          destruct (pattern_match (P_aux pat_aux _) (V_vector t)); (discriminate + apply L).
        * destruct_match; cbn; try suffix_solve.
    - cbn beta delta - [id_eqb] iota.
      fm_simp; try assumption.
      cbn in FD.
      rewrite forallb_forall in FD.
      rewrite Forall_forall.
      assumption.
    - cbn beta delta - [id_eqb] iota.
      fm_simp; try assumption.
      cbn in FD.
      rewrite forallb_forall in FD.
      rewrite Forall_forall.
      assumption.
    - reintros IHp1 IHp2 v FD.
      cbn beta delta - [id_eqb] iota.
      fm_simp; cbn in FD; rewrite andb_true_iff in FD.
      + reintros tl _ _ FD _ _ ? ?.
        specialize (IHp2 (V_list tl)).
        cbn in IHp2.
        destruct FD as [_ FD_tl].
        apply IHp2 in FD_tl.
        destruct (pattern_match _ (V_list tl)); cbn in FD_tl.
        * discriminate.
        * tauto.
        * discriminate.
      + destruct FD.
        solve_fd.
      + destruct FD.
        solve_fd.
    - cbn beta delta - [id_eqb merge_match_result] iota.
      destruct v; try reflexivity.
      reintros IH fields FD.
      rewrite struct_fdm_helper.
      fm_simp; apply (fun P => Forall_impl_in _ P IH); intros fld In_fields Q m fvs FD_m Drop.
      unfold MatcherResult; split.
      + unfold merge_match_result.
        fm_simp; try apply FD_m.
        lazymatch goal with
        | [ name : id |- _ ] => rename name into i
        end.
        cbn in FD.
        specialize (Q (get_struct_field i fvs)).
        assert (L : fully_defined (get_struct_field i fvs) = true).
        {
          apply fully_defined_struct_field.
          apply (Suffix_forallb Drop).
          unfold snd.
          apply forallb_forall; intros fv In.
          rewrite forallb_forall in FD.
          specialize (FD fv In).
          destruct fv.
          exact FD.
        }
        apply Q in L.
        cbn in L. solve_fd.
      + destruct fld; unfold Suffix.
        exists 0.
        reflexivity.
  Qed.

End Make.
