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

From Stdlib Require Import String.

From stdpp Require Import base.

From Sail Require Import Ast.
From Sail Require Import AstInduction.
From Sail Require Import IdUtil.
From Sail Require Import ListUtil.
From Sail Require Import OptionUtil.
From Sail Require Import Tactics.
From Sail Require Import ValueType.
From Sail Require Import Domain.Lattice.
From Sail Require Domain.AbsValue.
From Sail Require Domain.AbsBitvector.
From Sail Require Domain.Interval.
From Sail Require PatternMatch.
From Sail Require TypeAnnot.

(**
We start by re-defining l-expressions such that they contain no
embedded expressions. The type [zlexp A] is like [lexp A] but
essentially contains an implicit 'hole' wherever an expression would
have gone. See the [nat] argument for the [LZ_app] constructor, which
is the number of holes for an illustrative example of this in action.

The end goal is to be able to losslessly transform [lexp A] into
[zlexp A * list (exp A)] and back again.
*)

Inductive zlexp_aux {A : Set} : Set :=
| LZ_id : id → zlexp_aux
| LZ_deref : zlexp_aux
| LZ_app : id → nat → zlexp_aux
| LZ_typ : typ → id → zlexp_aux
| LZ_tuple : list zlexp → zlexp_aux
| LZ_vector_concat : list zlexp → zlexp_aux
| LZ_vector : zlexp → zlexp_aux
| LZ_vector_range : zlexp → zlexp_aux
| LZ_field : zlexp → id → zlexp_aux

with zlexp {A : Set} : Set :=
| LZ_aux : zlexp_aux → annot A → zlexp.

Arguments zlexp_aux A : clear implicits.
Arguments zlexp A : clear implicits.

Fixpoint lexp_to_z {A : Set} (l : lexp A) : zlexp A :=
  let 'LE_aux aux ann := l in
  match aux with
  | LE_id id => LZ_aux (LZ_id id) ann
  | LE_typ typ id => LZ_aux (LZ_typ typ id) ann
  | LE_deref _ => LZ_aux LZ_deref ann
  | LE_app id args => LZ_aux (LZ_app id (List.length args)) ann
  | LE_tuple ls => LZ_aux (LZ_tuple (map lexp_to_z ls)) ann
  | LE_vector_concat ls =>
      LZ_aux (LZ_vector_concat (map lexp_to_z ls)) ann
  | LE_vector l _ => LZ_aux (LZ_vector (lexp_to_z l)) ann
  | LE_vector_range l _ _ => LZ_aux (LZ_vector_range (lexp_to_z l)) ann
  | LE_field l f => LZ_aux (LZ_field (lexp_to_z l) f) ann
  end.

Fixpoint update_zlexp_subexps {A : Set} (xs : list (exp A)) (l : zlexp A) : option (lexp A) * list (exp A) :=
  let 'LZ_aux aux annot := l in
  match aux with
  | LZ_id id => (Some (LE_aux (LE_id id) annot), xs)
  | LZ_typ typ id => (Some (LE_aux (LE_typ typ id) annot), xs)
  | LZ_deref =>
      match xs with
      | y :: ys =>
          (Some (LE_aux (LE_deref y) annot), ys)
      | _ => (None, xs)
      end
  | LZ_field l fld =>
      match update_zlexp_subexps xs l with
      | (None, xs') => (None, xs')
      | (Some l', xs') => (Some (LE_aux (LE_field l' fld) annot), xs')
      end
  | LZ_tuple ls =>
      match fold_left (consume update_zlexp_subexps) ls (Some [], xs) with
      | (Some ls, xs) => (Some (LE_aux (LE_tuple (List.rev ls)) annot), xs)
      | (None, xs) => (None, xs)
      end
  | LZ_vector_concat ls =>
      match fold_left (consume update_zlexp_subexps) ls (Some [], xs) with
      | (Some ls, xs) => (Some (LE_aux (LE_vector_concat (List.rev ls)) annot), xs)
      | (None, xs) => (None, xs)
      end
  | LZ_app id n =>
      let '(ys, zs) := take_drop n xs in
      (Some (LE_aux (LE_app id ys) annot), zs)
  | LZ_vector l =>
      match update_zlexp_subexps xs l with
      | (Some l, n :: xs) => (Some (LE_aux (LE_vector l n) annot), xs)
      | _ => (None, [])
      end
  | LZ_vector_range l =>
      match update_zlexp_subexps xs l with
      | (Some l, n :: m :: xs) => (Some (LE_aux (LE_vector_range l n m) annot), xs)
      | _ => (None, [])
      end
  end.

Lemma update_zlexp_identity_g : ∀ {A} (l : lexp A) (es : list (exp A)),
  update_zlexp_subexps (lexp_subexps l ++ es) (lexp_to_z l) = (Some l, es).
Proof with reflexivity.
  intros A l.
  induction l using lexp_ind_g.
  all: try reflexivity.
  - cbn; intros; rewrite take_drop_app...
  - induction ls as [| l ls].
    + reflexivity.
    + rewrite Forall_cons_iff in H.
      destruct H as [Hhd Htl].
      specialize (IHls Htl).
      intros es.
      cbn.
      rewrite <- app_assoc.
      rewrite Hhd.
      cbn in IHls.
      specialize (IHls es).
      rewrite foldl_consume.
      destruct (fold_left (consume update_zlexp_subexps)
         (map lexp_to_z ls)
         (Some [], List.concat (map lexp_subexps ls) ++ es)) as [o].
      destruct o as [rs' |].
      * rewrite rev_app_distr.
        inversion IHls...
      * discriminate.
  - induction ls as [| l ls].
    + reflexivity.
    + rewrite Forall_cons_iff in H.
      destruct H as [Hhd Htl].
      specialize (IHls Htl).
      intros es.
      cbn.
      rewrite <- app_assoc.
      rewrite Hhd.
      cbn in IHls.
      specialize (IHls es).
      rewrite foldl_consume.
      destruct (fold_left (consume update_zlexp_subexps)
         (map lexp_to_z ls)
         (Some [], List.concat (map lexp_subexps ls) ++ es)) as [o].
      destruct o as [rs' |].
      * rewrite rev_app_distr.
        inversion IHls...
      * discriminate.
  - cbn; intros; rewrite <- app_assoc; rewrite IHl...
  - cbn; intros; rewrite <- app_assoc; rewrite IHl...
  - cbn; intros; rewrite IHl...
Qed.

(**
Now we can prove the key property for the [zlexp] type, that we can
map it to and from an l-expression [l].
*)
Lemma update_zlexp_identity : ∀ {A} (l : lexp A),
  update_zlexp_subexps (lexp_subexps l) (lexp_to_z l) = (Some l, []).
Proof.
  intros A l.
  pose proof (update_zlexp_identity_g l []) as H.
  rewrite app_nil_r in H.
  exact H.
Qed.

(**
Now we define a 'zipper' type [zexp] for the Sail expression ([exp])
type.

Note that unlike a traditional zipper for a genric list or tree, we can't
traverse the zipper in any order. The only valid traversal order is
exactly the evaluation order demanded by Sail. A traditional list
zipper might look like:

<<
Inductive zipper {A} : Type := list A * A * list A
>>

where we can traverse either left or right by moving the focus (middle
element above). In the [zexp] type, this looks more like:

<<
Inductive zipper {R A} : Type := list R * (R + exp A) * list (exp A)
>>

So the focus is always either an unevaluated expression or some type
representing a partially/fully evaluated expression [R] - hence we can
only move left to right as we evaluate, turning [exp A] into [R].

To make it not horribly blow up in size, we factor out related
expressions with similar control-flow rules, so all two-argument
left-to-right evaluation contstructors are handled by [Z_pair_1] and
[Z_pair_2]. We also flatten the [exp] type, by inlining the auxilliary
[pexp] type, and changing the [lexp] type into the [zlexp] type we've
just defined. This avoids any of the mutual recursion that would make
defining this type awkward.
*)

Inductive single_case : Set :=
| Field : id → single_case
| Internal_assume : n_constraint → single_case
| Internal_return : single_case
| Throw : single_case
| Typ : typ → single_case.

Inductive pair_case : Set :=
| Assert : pair_case
| Vector_append : pair_case
| Cons : pair_case.

Inductive list_case : Set :=
| List : list_case
| Tuple : list_case
| Vector : list_case.

Inductive match_case : Set :=
| Match : match_case
| Letbind : match_case
| Try : match_case
| Internal_plet : match_case.

Inductive zexp_aux {V : Type} {R : Set} {S : Type} {A : Set} : Type :=
| Z_single : zexp → single_case → zexp_aux
| Z_return : zexp → zexp_aux
| Z_exit : zexp → zexp_aux
| Z_pair_1 : zexp → pair_case → exp A → zexp_aux
| Z_pair_2 : zexp → pair_case → R → zexp_aux
| Z_list : zexp → list_case → list R → list (exp A) → zexp_aux
| Z_app : zexp → id → list R → list (exp A) → zexp_aux
| Z_block : zexp → list R → list (exp A) → zexp_aux
| Z_if_cond : zexp → exp A → exp A → zexp_aux
| Z_if_then : zexp → S * R → exp A → zexp_aux
| Z_if_else : zexp → R → S * R → zexp_aux
| Z_match_head : zexp →
                 match_case →
                 list (S * pat A * option R * R) →
                 option (list (pat A * option (exp A) * exp A)) →
                 zexp_aux
| Z_match_arms_guard : zexp →
                       match_case →
                       V →
                       S * R →
                       list (S * pat A * option R * R) →
                       pat A →
                       bool →
                       exp A →
                       option (list (pat A * option (exp A) * exp A)) →
                       zexp_aux
| Z_match_arms_body : zexp →
                      match_case →
                      V →
                      S * R →
                      list (S * pat A * option R * R) →
                      pat A →
                      option R →
                      option (list (pat A * option (exp A) * exp A)) →
                      zexp_aux
| Z_assign_left : zexp → zlexp A → list R → list (exp A) → exp A → zexp_aux
| Z_assign_right : zexp → zlexp A → list R → zexp_aux
| Z_var_left : zexp → zlexp A → list R → list (exp A) → exp A → exp A → zexp_aux
| Z_var_right : zexp → zlexp A → list R → exp A → zexp_aux
| Z_var_body : zexp → zlexp A → list R → R → zexp_aux

with zexp {V : Type} {R : Set} {S : Type} {A : Set} : Type :=
| Z_aux : zexp_aux → annot A → zexp
| Z_top : zexp.

Arguments zexp_aux V R S A : clear implicits.
Arguments zexp V R S A : clear implicits.

Definition unwrap_arm {A : Set} (arm : pexp A) : pat A * option (exp A) * exp A :=
  match arm with
  | Pat_aux (Pat_exp pat body) _ => (pat, None, body)
  | Pat_aux (Pat_when pat guard body) _ => (pat, Some guard, body)
  end.

(**
As we partially evaluate expressions, we can compute a reduced
(residual) expression of (OCaml) type << Builder(Tannot).t >>. We can
avoid the cost of doing this by instantiating this type as [unit]
using the [UnitBuilder] module - In this case our partial evaluator
just becomes a regular (but symbolic) evaluator.

We also define the obvious [ExpBuilder] module that actually builds Sail
expressions.

One gotcha with this module is that all the lists are provided in
reverse order, so [mk_list ann Tuple [x; y; z]] will construct
[E_aux (E_tuple [z; y; x]) ann]. This is because the evaluator conses
newly evaluated items to lists of evaluated items [e :: es], rather
than appending them [es ++ [e]] (as this would be slower). In the
UnitBuilder case, we then completely skip the cost of reversing
the lists.
*)

Module Type Builder (Tannot : TypeAnnot.S).
  Parameter t : Set.

  Parameter mk_app     : annot Tannot.t → id → list t → t.
  Parameter mk_config  : annot Tannot.t → list string → t.
  Parameter mk_id      : annot Tannot.t → id → t.
  Parameter mk_block   : annot Tannot.t → list t → t.
  Parameter mk_exit    : annot Tannot.t → t → t.
  Parameter mk_ite     : annot Tannot.t → t → t → t → t.
  Parameter mk_list    : annot Tannot.t → list_case → list t → t.
  Parameter mk_literal : annot Tannot.t → lit → t.
  Parameter mk_match   : annot Tannot.t → match_case → t → list (pat Tannot.t * option t * t) → t.
  Parameter mk_pair    : annot Tannot.t → pair_case → t → t → t.
  Parameter mk_ref     : annot Tannot.t → id → t.
  Parameter mk_return  : annot Tannot.t → t → t.
  Parameter mk_single  : annot Tannot.t → single_case → t → t.
  Parameter mk_var     : annot Tannot.t → zlexp Tannot.t → list t → t → t → t.
  Parameter mk_assign  : annot Tannot.t → zlexp Tannot.t → list t → t → t.
  Parameter mk_undef   : annot Tannot.t → t.
End Builder.

Module UnitBuilder (Tannot : TypeAnnot.S) <: Builder(Tannot).
  Definition t := unit.

  Definition mk_app     (_ : annot Tannot.t) (_ : id) (_ : list t) := tt.
  Definition mk_config  (_ : annot Tannot.t) (_ : list string) := tt.
  Definition mk_id      (_ : annot Tannot.t) (_ : id) := tt.
  Definition mk_block   (_ : annot Tannot.t) (_ : list t) := tt.
  Definition mk_exit    (_ : annot Tannot.t) (_ : t) := tt.
  Definition mk_ite     (_ : annot Tannot.t) (_ : t) (_ : t) (_ : t) := tt.
  Definition mk_list    (_ : annot Tannot.t) (_ : list_case) (_ : list t) := tt.
  Definition mk_literal (_ : annot Tannot.t) (_ : lit) := tt.
  Definition mk_match   (_ : annot Tannot.t) (_ : match_case) (_ : t) (_ : list (pat Tannot.t * option t * t)) := tt.
  Definition mk_pair    (_ : annot Tannot.t) (_ : pair_case) (_ : t) (_ : t) := tt.
  Definition mk_ref     (_ : annot Tannot.t) (_ : id) := tt.
  Definition mk_return  (_ : annot Tannot.t) (_ : t) := tt.
  Definition mk_single  (_ : annot Tannot.t) (_ : single_case) (_ : t) := tt.
  Definition mk_var     (_ : annot Tannot.t) (_ : zlexp Tannot.t) (_ : list t) (_ : t) (_ : t) := tt.
  Definition mk_assign  (_ : annot Tannot.t) (_ : zlexp Tannot.t) (_ : list t) (_ : t) := tt.
  Definition mk_undef   (_ : annot Tannot.t) := tt.
End UnitBuilder.

Module ExpBuilder (Tannot : TypeAnnot.S) <: Builder(Tannot).
  Definition t := exp Tannot.t.

  Definition mk_app (ann : annot Tannot.t) (f : id) (xs : list t) := E_aux (E_app f xs) ann.

  Definition mk_config (ann : annot Tannot.t) (key : list string) := E_aux (E_config key) ann.

  Definition mk_id (ann : annot Tannot.t) (id : id) := E_aux (E_id id) ann.

  Definition mk_block (ann : annot Tannot.t) (exps : list t) := E_aux (E_block (List.rev exps)) ann.

  Definition mk_exit (ann : annot Tannot.t) (x : t) := E_aux (E_exit x) ann.

  Definition mk_ite (ann : annot Tannot.t) (iexp : t) (texp : t) (eexp : t) := E_aux (E_if iexp texp eexp) ann.

  Definition mk_list (ann : annot Tannot.t) (c : list_case) (xs : list t) :=
    match c with
    | List => E_aux (E_list (List.rev xs)) ann
    | Tuple => E_aux (E_tuple (List.rev xs)) ann
    | Vector => E_aux (E_vector (List.rev xs)) ann
    end.

  Definition mk_literal (ann : annot Tannot.t) (l : lit) := E_aux (E_lit l) ann.

  Definition mk_pexp (ann : annot Tannot.t) (arm : pat Tannot.t * option t * t) :=
    let '(pat, guard_opt, body) := arm in
    match guard_opt with
    | None   => Pat_aux (Pat_exp pat body) ann
    | Some g => Pat_aux (Pat_when pat g body) ann
    end.

  Definition mk_match (ann : annot Tannot.t) (c : match_case) (head_exp : t) (arms : list (pat Tannot.t * option t * t)) :=
    match c with
    | Try => E_aux (E_try head_exp (List.map (mk_pexp ann) arms)) ann
    | Match | Letbind =>
        match arms with
        | [(pat, None, body)] =>
            E_aux (E_let pat head_exp body) ann
        | _ => E_aux (E_match head_exp (List.map (mk_pexp ann) arms)) ann
        end
    | Internal_plet =>
        match arms with
        | [(pat, None, body)] =>
            E_aux (E_internal_plet pat head_exp body) ann
        | _ => E_aux (E_match head_exp (List.map (mk_pexp ann) arms)) ann
        end
    end.

  Definition mk_pair (ann : annot Tannot.t) (c : pair_case) (x : t) (y : t) :=
    match c with
    | Assert => E_aux (E_assert x y) ann
    | Cons => E_aux (E_cons x y) ann
    | Vector_append => E_aux (E_vector_append x y) ann
    end.

  Definition mk_ref (ann : annot Tannot.t) (reg : id) := E_aux (E_ref reg) ann.

  Definition mk_return (ann : annot Tannot.t) (x : t) := E_aux (E_return x) ann.

  Definition mk_single (ann : annot Tannot.t) (c : single_case) (x : t) :=
    match c with
    | Field fld => E_aux (E_field x fld) ann
    | Internal_assume nc => E_aux (E_internal_assume nc x) ann
    | Internal_return => E_aux (E_return x) ann
    | Throw => E_aux (E_throw x) ann
    | Typ typ => E_aux (E_typ typ x) ann
    end.

  Definition mk_var (ann : annot Tannot.t) (l : zlexp Tannot.t) (args : list t) (x : t) (body : t) :=
    match update_zlexp_subexps args l with
    | (Some l', _) => E_aux (E_var l' x body) ann
    | _ => E_aux E_undef ann
    end.

  Definition mk_assign  (ann : annot Tannot.t) (l : zlexp Tannot.t) (args : list t) (x : t) :=
    match update_zlexp_subexps args l with
    | (Some l', _) => E_aux (E_assign l' x) ann
    | _ => E_aux E_undef ann
    end.

  Definition mk_undef (ann : annot Tannot.t) := E_aux E_undef ann.
End ExpBuilder.

Module Residual (Tannot : TypeAnnot.S) (B : Builder Tannot).
  Module L := AbsValue.Dom Interval.Dom AbsBitvector.Dom.

  Record value := {
      (* The actual value returned by some expression. [None] acts a
         bottom value for expressions that don't have a value like
         return and throw. *)
      this : option L.t;
      (* This value represents the set of possible exceptions returned
         by an expression. *)
      exn  : option L.t;
      (* Track whether the value came from a side-effecting
         expression. This effectively blocks most simplifications. *)
      eff  : bool;
    }.

  Record state := {
      locals    : IdMap.t L.t;
      registers : IdMap.t L.t;
    }.

  Definition t : Set := value * B.t.

  Definition is_unit (v : value) : bool :=
    option_is L.is_unit (this v) && is_none (exn v) && negb (eff v).

  Definition is_true (v : value) : bool :=
    option_is L.is_true (this v) && is_none (exn v) && negb (eff v).

  Definition is_false (v : value) : bool :=
    option_is L.is_false (this v) && is_none (exn v) && negb (eff v).

  Definition bounded_join (o₁ o₂ : option L.t) : option L.t := option_join L.join o₁ o₂.

  Infix "⊔" := bounded_join (no associativity, at level 50).
  Notation "⊥" := None.

  Open Scope bool_scope.

  Definition mk_block (ann : annot Tannot.t) (rs : list t) :=
    match rs with
    | [] => ({| this := Some L.V_unit; exn := ⊥; eff := false |}, B.mk_block ann [])
    | r :: _ => (
        {|
          this := this (fst r);
          exn  := List.fold_left bounded_join (List.map (fun r => exn (fst r)) rs) None;
          eff  := List.fold_left orb (List.map (fun r => eff (fst r)) rs) false
        |},
        B.mk_block ann (List.map snd rs)
      )
    end.

  Definition mk_exit (ann : annot Tannot.t) (r : t) :=
    ({| this := ⊥; exn := exn (fst r); eff := true |}, B.mk_exit ann (snd r)).

  Definition mk_ite (ann : annot Tannot.t) (ir tr er : t) :=
    match this (fst ir) with
    | None => ({| this := ⊥; exn := exn (fst ir); eff := eff (fst ir) |}, snd ir)
    | Some  _ => (
        {|
          this := this (fst tr) ⊔ this (fst er);
          exn  := exn (fst ir) ⊔ exn (fst tr) ⊔ exn (fst er);
          eff  := eff (fst ir) || eff (fst tr) || eff (fst er);
        |},
        B.mk_ite ann (snd ir) (snd tr) (snd er)
      )
    end.

  Definition mk_list (ann : annot Tannot.t) (c : list_case) (rs : list t) :=
    let ctor := match c with
      | List => L.V_list
      | Tuple => L.V_tuple
      | Vector => L.V_vector
      end
    in (
      {|
        this := option_map ctor (option_all (List.rev (List.map (fun r => this (fst r)) rs)));
        exn  := List.fold_left bounded_join (List.map (fun r => exn (fst r)) rs) ⊥;
        eff  := List.fold_left orb (List.map (fun r => eff (fst r)) rs) false
      |},
      B.mk_list ann c (List.map snd rs)
    ).

  Definition mk_literal (ann : annot Tannot.t) (l : lit) :=
    ({| this := Some (L.of_lit l); exn := ⊥; eff := false |}, B.mk_literal ann l).

  Definition build_arm (arm : state * pat Tannot.t * option t * t) : pat Tannot.t * option B.t * B.t :=
    let '(_, pat, guard_opt, body) := arm in
    (pat, option_map snd guard_opt, snd body).

  Definition exn_arm (arm : state * pat Tannot.t * option t * t) : option L.t :=
    let '(_, _, guard_opt, body) := arm in
    bounded_join (option_bind guard_opt (fun r => exn (fst r))) (exn (fst body)).

  Definition this_arm (arm : state * pat Tannot.t * option t * t) : option L.t :=
    let '(_, _, _, body) := arm in
    this (fst body).

  Definition eff_arm (arm : state * pat Tannot.t * option t * t) : bool :=
    let '(_, _, guard_opt, body) := arm in
    orb (match guard_opt with ⊥ => false | Some g => eff (fst g) end) (eff (fst body)).

  Definition mk_match (ann : annot Tannot.t)
                      (c : match_case)
                      (guaranteed_match : bool)
                      (head : t) (arms : list (state * pat Tannot.t * option t * t))
                    : t :=
    let b := B.mk_match ann c (snd head) (List.map build_arm arms) in
    match c with
    | Try =>
        let p :=
          if is_none (exn (fst head)) then
            {| this := this (fst head); exn := ⊥; eff := eff (fst head) |}
          else
            {|
              this := List.fold_left (fun acc arm => bounded_join acc (this_arm arm)) arms (this (fst head));
              exn  := if guaranteed_match
                      then List.fold_left (fun acc arm => bounded_join acc (exn_arm arm)) arms ⊥
                      else List.fold_left (fun acc arm => bounded_join acc (exn_arm arm)) arms (exn (fst head));
              eff  := List.fold_left (fun acc arm => orb acc (eff_arm arm)) arms (eff (fst head));
            |}
        in
        (p, b)
    | Match | Letbind | Internal_plet => (
        {|
          this := List.fold_left (fun acc arm => bounded_join acc (this_arm arm)) arms ⊥;
          exn  := List.fold_left (fun acc arm => bounded_join acc (exn_arm arm)) arms (exn (fst head));
          eff  := List.fold_left (fun acc arm => orb acc (eff_arm arm)) arms (eff (fst head));
        |},
        b
      )
    end.

  Definition mk_pair (ann : annot Tannot.t) (c : pair_case) (x : t) (y : t) :=
    let b := B.mk_pair ann c (snd x) (snd y) in
    match c with
    | Assert => ({| this := Some L.V_unit; exn := exn (fst x) ⊔ exn (fst y); eff := true |}, b)
    | Vector_append => ({| this := ⊥; exn := ⊥; eff := false |}, b)
    | Cons => ({| this := ⊥; exn := ⊥; eff := false |}, b)
    end.

  Definition mk_ref (ann : annot Tannot.t) (id : Ast.id) :=
    ({| this := Some (L.V_ref (Aux.unwrap id)); exn := ⊥; eff := false |}, B.mk_ref ann id).

  Definition mk_return (ann : annot Tannot.t) (r : t) :=
    ({| this := ⊥; exn := exn (fst r); eff := true |}, B.mk_return ann (snd r)).

  Definition mk_single (ann : annot Tannot.t) (c : single_case) (r : t) :=
    let b := B.mk_single ann c (snd r) in
    match c with
    | Field fld =>
        match this (fst r) with
        | Some rec =>
            ({| this := Some (L.lookup_field rec (Aux.unwrap fld)); exn := exn (fst r); eff := eff (fst r) |}, b)
        | ⊥ =>
            ({| this := ⊥; exn := exn (fst r); eff := eff (fst r) |}, b)
        end
    | Internal_assume _ => (fst r, b)
    | Internal_return => (fst r, b)
    | Throw => ({| this := ⊥; exn := bounded_join (this (fst r)) (exn (fst r)); eff := false |}, b)
    | Typ _ => (fst r, b)
    end.

  Definition mk_var (ann : annot Tannot.t) (zl : zlexp Tannot.t) (rs : list t) (exp : t) (body : t) :=
    (fst body, B.mk_var ann zl (List.map snd rs) (snd exp) (snd body)).

  Definition mk_assign (ann : annot Tannot.t) (zl : zlexp Tannot.t) (rs : list t) (exp : t) := (
      {|
        this := Some L.V_unit;
        exn := List.fold_left bounded_join (List.map (fun r => exn (fst r)) rs) (exn (fst exp));
        eff := true
      |},
      B.mk_assign ann zl (List.map snd rs) (snd exp)
    ).

  Definition empty : state := {| locals := IdMap.empty L.t; registers := IdMap.empty L.t |}.

  Definition join (σ₁ σ₂ : state) : state := {|
      locals := IdMap.map2 bounded_join (locals σ₁) (locals σ₂);
      registers := IdMap.map2 bounded_join (registers σ₁) (registers σ₂)
    |}.

  Definition from_semilattice (v : L.t) : value := {| this := Some v; exn := ⊥; eff := false |}.

  Definition pattern_match (l : Ast.l) (c : match_case) (pat : pat Tannot.t) (head_exp : t)
                         : Ast.loc + PatternMatch.match_result L.t :=
    let h := match c with
      | Try => exn (fst head_exp)
      | _ => this (fst head_exp)
      end
    in
    match h with
    | ⊥ => inl l
    | Some v => inl l (* FIXME: inr (L.pattern_match pat v) *)
    end.

  Definition end_match (c : match_case) (_ : option state) (_ : list state) : state := empty.

  Definition lookup (l : Ast.loc) (σ : state) (id : Ast.id) : Ast.loc + L.t :=
    match IdMap.find id (locals σ) with
    | Some v => inr v
    | ⊥ =>
        match IdMap.find id (registers σ) with
        | Some v => inr v
        | ⊥ => inl l
        end
    end.

  Definition assign (zl : zlexp Tannot.t) (rs : list t) (exp : t) (σ : state) : state := empty.
End Residual.

Module Make (Tannot : TypeAnnot.S) (B : Builder Tannot).
  Module R := Residual Tannot B.
  Module L := R.L.

  Module Monad.
    (* TODO: Find a way to share the monad with Semantics.v *)
    Inductive t {A : Type} : Type :=
    | Pure : A → t
    | Early_return : R.value → (unit → t) → t
    | Exit : R.value → (unit → t) → t
    | Call : id → list R.value → (R.value → t) → t
    | Get_config : list string → (R.value → t) → t
    | Runtime_type_error : Ast.loc → t
    | Get_undefined : typ → (R.value → t) → t.

    Arguments t A : clear implicits.

    Fixpoint bind {A B : Type} (m : t A) (f : A → t B) : t B :=
      match m with
      | Pure x => f x
      | Early_return v cont => Early_return v (fun v => bind (cont tt) f)
      | Exit v cont => Exit v (fun v => bind (cont tt) f)
      | Call id args cont => Call id args (fun v => bind (cont v) f)
      | Get_config key cont => Get_config key (fun v => bind (cont v) f)
      | Runtime_type_error l => Runtime_type_error l
      | Get_undefined t cont => Get_undefined t (fun v => bind (cont v) f)
      end.

    Definition lift_sum {A : Type} (mr : Ast.loc + A) : t A :=
      match mr with
      | inl l => Runtime_type_error l
      | inr r => Pure r
      end.
  End Monad.

  Notation "x ← y ; z" := (Monad.bind y (fun x : _ => z))
    (at level 20, y at level 100, z at level 200, only parsing).

  Definition pure {A : Type} (x : A) : Monad.t A := Monad.Pure x.

  Definition t := zexp (IdMap.t L.t) R.t R.state Tannot.t.

  Fixpoint lookup (ctx : t) (id : id) : option L.t :=
    match ctx with
    | Z_top => None
    | Z_aux aux annot =>
      match aux with
      | Z_single parent _
      | Z_return parent
      | Z_exit parent
      | Z_pair_1 parent _ _
      | Z_pair_2 parent _ _
      | Z_list parent _ _ _
      | Z_app parent _ _ _
      | Z_block parent _ _
      | Z_if_cond parent _ _
      | Z_if_then parent _ _
      | Z_if_else parent _ _
      | Z_match_head parent _ _ _
      | Z_assign_left parent _ _ _ _
      | Z_assign_right parent _ _
      | Z_var_left parent _ _ _ _ _
      | Z_var_right parent _ _ _
      | Z_var_body parent _ _ _ => lookup parent id

      | Z_match_arms_guard parent _ β _ _ _ _ _ _
      | Z_match_arms_body parent _ β _ _ _ _ _ =>
          match IdMap.find id β with
          | Some v => Some v
          | None => lookup parent id
          end
      end
    end.

  Definition down (ctx : t)
                  (σ : R.state)
                  (focus : exp Tannot.t)
                : Monad.t (t * R.state * (exp Tannot.t + R.t)) :=
    let 'E_aux aux annot := focus in
    let wrap aux exp := pure (Z_aux aux annot, σ, inl exp) in
    match aux with
    | E_id i =>
        match lookup ctx i with
        | Some v => pure (ctx, σ, inr (R.from_semilattice v, B.mk_id annot i))
        | None =>
            v ← Monad.lift_sum (R.lookup (fst annot) σ i);
            pure (ctx, σ, inr (R.from_semilattice v, B.mk_id annot i))
        end
    | E_lit lit => pure (ctx, σ, inr (R.mk_literal annot lit))
    | E_if i t e => wrap (Z_if_cond ctx t e) i
    | E_match head arms => wrap (Z_match_head ctx Match [] (Some (List.map unwrap_arm arms))) head
    | E_try head arms => wrap (Z_match_head ctx Try [] (Some (List.map unwrap_arm arms))) head
    | E_let pat exp body => wrap (Z_match_head ctx Letbind [] (Some [(pat, None, body)])) exp
    | E_internal_plet pat exp body => wrap (Z_match_head ctx Internal_plet [] (Some [(pat, None, body)])) exp
    | E_app f xs =>
        match xs with
        | x :: xs => wrap (Z_app ctx f [] xs) x
        | [] =>
            r ← Monad.Call f [] pure;
            pure (ctx, σ, inr (r, B.mk_app annot f []))
        end
    | E_typ t exp => wrap (Z_single ctx (Typ t)) exp
    | E_tuple exps =>
        match exps with
        | [] => pure (ctx, σ, inr (R.mk_list annot Tuple []))
        | exp :: exps => wrap (Z_list ctx Tuple [] exps) exp
        end
    | E_vector exps =>
        match exps with
        | [] => pure (ctx, σ, inr (R.mk_list annot Vector []))
        | exp :: exps => wrap (Z_list ctx Vector [] exps) exp
        end
    | E_list exps =>
        match exps with
        | [] => pure (ctx, σ, inr (R.mk_list annot List []))
        | exp :: exps => wrap (Z_list ctx List [] exps) exp
        end
    | E_vector_append l r => wrap (Z_pair_1 ctx Vector_append r) l
    | E_cons h t => wrap (Z_pair_1 ctx Cons t) h
    | E_assert exp msg => wrap (Z_pair_1 ctx Assert msg) exp
    | E_field exp fld => wrap (Z_single ctx (Field fld)) exp
    | E_return exp => wrap (Z_return ctx) exp
    | E_exit exp => wrap (Z_exit ctx) exp
    | E_ref id => pure (ctx, σ, inr (R.mk_ref annot id))
    | E_throw exp => wrap (Z_single ctx Throw) exp
    | E_config key =>
        v ← Monad.Get_config key pure;
        pure (ctx, σ, inr (v, B.mk_config annot key))
    | E_block exps =>
        match exps with
        | [] => pure (ctx, σ, inr (R.mk_block annot []))
        | exp :: exps => wrap (Z_block ctx [] exps) exp
        end
    | E_internal_assume constr exp => wrap (Z_single ctx (Internal_assume constr)) exp
    | E_internal_return exp => wrap (Z_single ctx Internal_return) exp
    | E_undef =>
        u ← Monad.Get_undefined (Tannot.get_type (snd annot)) pure;
        pure (ctx, σ, inr (u, B.mk_undef annot))
    | E_assign l exp =>
        let subexps := lexp_subexps l in
        match subexps with
        | []      => wrap (Z_assign_right ctx (lexp_to_z l) []) exp
        | x :: xs => wrap (Z_assign_left ctx (lexp_to_z l) [] xs exp) x
        end
    | E_var l exp body =>
        let subexps := lexp_subexps l in
        match subexps with
        | []      => wrap (Z_var_right ctx (lexp_to_z l) [] body) exp
        | x :: xs => wrap (Z_var_left ctx (lexp_to_z l) [] xs exp body) x
        end

    | E_struct _ _ | E_struct_update _ _ | E_for _ _ _ _ _ _ | E_loop _ _ _ _ => Monad.Runtime_type_error (fst annot)

    | E_sizeof _ | E_constraint _ | E_internal_value _ => Monad.Runtime_type_error (fst annot)
    end.

  Definition next (aux : zexp_aux (IdMap.t L.t) R.t R.state Tannot.t)
                  (annot : annot Tannot.t)
                  (σ : R.state)
                  (focus : R.t)
                : Monad.t (t * R.state * (exp Tannot.t + R.t)) :=
    match aux with
    | Z_if_cond parent t e =>
        if R.is_true (fst focus) then
          pure (parent, σ, inl t)
        else if R.is_false (fst focus) then
          pure (parent, σ, inl e)
        else
          pure (Z_aux (Z_if_then parent (σ, focus) e) annot, σ, inl t)
    | Z_if_then parent (σ_i, i) e =>
        pure (Z_aux (Z_if_else parent i (σ, focus)) annot, σ_i, inl e)
    | Z_if_else parent i (σ_t, t) =>
        pure (parent, R.join σ_t σ, inr (R.mk_ite annot i t focus))

    | Z_single parent γ =>
        pure (parent, σ, inr (R.mk_single annot γ focus))

    | Z_return parent =>
        _ ← Monad.Early_return (fst focus) pure;
        pure (parent, σ, inr (R.mk_return annot focus))

    | Z_exit parent =>
        _ ← Monad.Exit (fst focus) pure;
        pure (parent, σ, inr (R.mk_exit annot focus))

    | Z_pair_1 parent γ y =>
        pure (Z_aux (Z_pair_2 parent γ focus) annot, σ, inl y)
    | Z_pair_2 parent γ x =>
        pure (parent, σ, inr (R.mk_pair annot γ x focus))

    | Z_list parent γ evaluated unevaluated =>
        match unevaluated with
        | []      => pure (parent, σ, inr (R.mk_list annot γ (focus :: evaluated)))
        | u :: us => pure (Z_aux (Z_list parent γ (focus :: evaluated) us) annot, σ, inl u)
        end

    | Z_block parent evaluated unevaluated =>
        match unevaluated with
        | []      => pure (parent, σ, inr (R.mk_block annot (focus :: evaluated)))
        | u :: us =>
            if R.is_unit (fst focus) then
              pure (Z_aux (Z_block parent evaluated us) annot, σ, inl u)
            else
              pure (Z_aux (Z_block parent (focus :: evaluated) us) annot, σ, inl u)
        end

    | Z_app parent f evaluated unevaluated =>
        match unevaluated with
        | [] =>
            r ← Monad.Call f [] (* FIXME (focus :: evaluated) *) pure;
            pure (parent, σ, inr (r, B.mk_app annot f (List.map snd evaluated)))
        | u :: us => pure (Z_aux (Z_app parent f (focus :: evaluated) us) annot, σ, inl u)
        end

    | Z_match_head parent γ evaluated unevaluated =>
        match unevaluated with
        (* This None if we know for sure that one of the arms must have matched. *)
        | None    => pure (parent, R.end_match γ None     (List.map (fun '(σ, _, _, _) => σ) evaluated), inr (R.mk_match annot γ true focus evaluated))
        (* We've evaluated all the arms, but it's possible we've fallen off the end of the match. *)
        | Some [] => pure (parent, R.end_match γ (Some σ) (List.map (fun '(σ, _, _, _) => σ) evaluated), inr (R.mk_match annot γ false focus evaluated))
        (* Start evaluating the next possible arm, by binding it's pattern. *)
        | Some ((pat, guard, body) :: arms) =>
            mr ← Monad.lift_sum (R.pattern_match (fst annot) γ pat focus);
            match mr with
            | PatternMatch.Unmatched =>
                pure (Z_aux (Z_match_head parent γ evaluated (Some arms)) annot, σ, inr focus)
            | PatternMatch.Matched β =>
                let β := IdMap.map L.complete β in
                match guard with
                | None =>
                    pure (Z_aux (Z_match_arms_body parent γ β (σ, focus) evaluated pat None None) annot, σ, inl body)
                | Some g =>
                    pure (Z_aux (Z_match_arms_guard parent γ β (σ, focus) evaluated pat true body None) annot, σ, inl g)
                end
            | PatternMatch.MaybeMatched β =>
                let β := IdMap.map L.complete β in
                match guard with
                | None =>
                    pure (Z_aux (Z_match_arms_body parent γ β (σ, focus) evaluated pat None (Some arms)) annot, σ, inl body)
                | Some g =>
                    pure (Z_aux (Z_match_arms_guard parent γ β (σ, focus) evaluated pat false body (Some arms)) annot, σ, inl g)
                end
            end
        end
    | Z_match_arms_guard parent γ β (σ_h, h) evaluated pat guaranteed_match body unevaluated =>
        if R.is_true (fst focus) then
          (* If the pattern before the guard was a guaranteed match, and the guard is always true, we can
             discard the rest of the unevaluated arms. *)
          let unevaluated' := if guaranteed_match then None else unevaluated in
          pure (Z_aux (Z_match_arms_body parent γ β (σ_h, h) evaluated pat None unevaluated') annot, σ, inl body)
        else if R.is_false (fst focus) then
          pure (Z_aux (Z_match_head parent γ evaluated unevaluated) annot, σ_h, inr h)
        else
          pure (Z_aux (Z_match_arms_body parent γ β (σ_h, h) evaluated pat (Some focus) unevaluated) annot, σ, inl body)
    | Z_match_arms_body parent γ β (σ_h, h) evaluated pat guard unevaluated =>
        pure (Z_aux (Z_match_head parent γ ((σ, pat, guard, focus) :: evaluated) unevaluated) annot, σ_h, inr h)

    | Z_assign_left parent l evaluated unevaluated exp =>
        match unevaluated with
        | [] => pure (Z_aux (Z_assign_right parent l evaluated) annot, σ, inl exp)
        | u :: us => pure (Z_aux (Z_assign_left parent l (focus :: evaluated) us exp) annot, σ, inl u)
        end
    | Z_assign_right parent l evaluated =>
        pure (parent, R.assign l evaluated focus σ, inr (R.mk_assign annot l evaluated focus))

    | Z_var_left parent l evaluated unevaluated exp body =>
        match unevaluated with
        | [] => pure (Z_aux (Z_var_right parent l evaluated body) annot, σ, inl exp)
        | u :: us => pure (Z_aux (Z_var_left parent l (focus :: evaluated) us exp body) annot, σ, inl u)
        end
    | Z_var_right parent l evaluated body =>
        pure (Z_aux (Z_var_body parent l evaluated focus) annot, R.assign l evaluated focus σ, inl body)
    | Z_var_body parent l evaluated v =>
        pure (parent, σ, inr (R.mk_var annot l evaluated v focus))
    end.

  Definition step (ctx : t)
                  (σ : R.state)
                  (focus : exp Tannot.t + R.t)
                : Monad.t (t * R.state * (exp Tannot.t + R.t)) :=
    match focus with
    | inl exp => down ctx σ exp
    | inr v  =>
        match ctx with
        | Z_top => pure (Z_top, σ, inr v)
        | Z_aux aux annot => next aux annot σ v
        end
    end.
End Make.
