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

From stdpp Require Import base.

From Sail Require Import Tactics.
From Sail Require Import Ast.
From Sail Require Import AstInduction.
From Sail Require Import Bit.
From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import ValueType.

From Sail Require BitList.
From Sail Require TypeAnnot.

Import TypeAnnot.Types.

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
| Complete : value → binding V
| Partial : non_empty (V * Z * Z) → binding V.

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

Lemma binding_part_eqb_refl : ∀ p, binding_part_eqb p p = true.
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

Lemma binding_eqb_refl : ∀ b, binding_eqb b b = true.
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

Lemma combine_binding_none_left : ∀ {V} (b : option (binding V)), combine_binding None b = b.
Proof.
  intros ? b; destruct b; cbn; reflexivity.
Qed.

Lemma combine_binding_none_right : ∀ {V} (b : option (binding V)), combine_binding b None = b.
Proof.
  intros ? b; destruct b; cbn; reflexivity.
Qed.

Lemma combine_binding_assoc : ∀ {V} (a b c : option (binding V)), combine_binding (combine_binding a b) c = combine_binding a (combine_binding b c).
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

Lemma merge_bindings_in_left : ∀ {V k} {x y : IdMap.t (binding V)},
  IdMap.In k x → IdMap.In k (merge_bindings x y).
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

Lemma merge_bindings_in_right : ∀ {V k} {y x : IdMap.t (binding V)}, IdMap.In k y → IdMap.In k (merge_bindings x y).
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

Lemma merge_bindings_in_iff : ∀ {V k} {x y : IdMap.t (binding V)}, IdMap.In k (merge_bindings x y) ↔ IdMap.In k x ∨ IdMap.In k y.
Proof.
  intros ? k x y.
  split; intros H.
  - unfold merge_bindings.
    apply (IdMap.map2_2 H).
  - destruct H as [Hx | Hy].
    + apply (merge_bindings_in_left Hx).
    + apply (merge_bindings_in_right Hy).
Qed.

Lemma not_in_map2 : ∀ A k (x y : IdMap.t A) f, ~ IdMap.In k x → ~ IdMap.In k y → ~ IdMap.In (elt:=A) k (IdMap.map2 f x y).
Proof.
  intros A k x y f Not_in_x Not_in_y.
  unfold not.
  intros In_xy.
  apply IdMap.map2_2 in In_xy.
  tauto.
Qed.

Lemma not_in_find_none : ∀ [A k] (x : IdMap.t A), ~ IdMap.In k x ↔ IdMap.find k x = None.
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

Lemma map2_none_none : ∀ [A k] (x y : IdMap.t A) f,
  IdMap.find k x = None →
  IdMap.find k y = None →
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

  | [ H : IdMap.find ?k ?x = None |- IdMap.In ?k ?x ∨ IdMap.In ?k _ ] => apply or_intror
  | [ H : IdMap.find ?k ?y = None |- IdMap.In ?k _ ∨ IdMap.In ?k ?y ] => apply or_introl
  | [ H : IdMap.find ?k ?x = Some _ |- IdMap.In ?k ?x ∨ IdMap.In ?k _ ] => apply or_introl
  | [ H : IdMap.find ?k ?y = Some _ |- IdMap.In ?k _ ∨ IdMap.In ?k ?y ] => apply or_intror

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

Lemma merge_bindings_assoc : ∀ x y z,
  IdMap.Equivb binding_eqb (merge_bindings (merge_bindings x y) z) (merge_bindings x (merge_bindings y z)).
Proof.
  intros x y z.
  split.

  - intro k.
    change (IdMap.In k (merge_bindings (merge_bindings x y) z) ↔ IdMap.In k (merge_bindings x (merge_bindings y z))).
    repeat rewrite merge_bindings_in_iff.
    rewrite Logic.or_assoc.
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
| Matched : IdMap.t (binding V) → match_result
| MaybeMatched : IdMap.t (binding V) → match_result
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

Lemma merge_match_result_assoc : ∀ a b c, match_result_eq ((a ⋈ b) ⋈ c) (a ⋈ (b ⋈ c)).
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
      (f : pat Tannot.t → value → match_result value)
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
        | V_unit => simple_match
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
End Make.
