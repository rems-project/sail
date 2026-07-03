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
From Stdlib Require Import BinInt.
From Stdlib Require Import BinNat.

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
From Sail Require Domain.TransferBitvectorInterval.
From Sail Require PatternMatch.
From Sail Require TypeAnnot.

(**
We start by re-defining l-expressions such that they contain no
embedded expressions. The type [zlexp A] is like [lexp A] but
essentially contains an implicit 'hole' wherever an expression would
have gone.

The end goal is to be able to losslessly transform [lexp A] into
[zlexp A * list (exp A)] and back again.
*)

Inductive zlexp_aux {A : Set} : Set :=
| LZ_id : id → zlexp_aux
| LZ_deref : zlexp_aux
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
| Vector : list_case
| Bitvector : list_case.

Inductive match_case : Set :=
| Match : match_case
| Letbind : match_case
| Try : match_case
| Internal_plet : match_case.

Inductive zexp_aux {V : Type} {R : Set} {S : Type} {A : Set} : Type :=
| Z_single : zexp → single_case → zexp_aux
| Z_return : zexp → zexp_aux
(* The [option R] accumulates the join of every value the inlined function body
   has [return]ed early, so that returns from speculative branches are joined
   rather than escaping the whole computation. *)
| Z_inline : zexp → option R → zexp_aux
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
| Z_struct : zexp → struct_name → list (id * R) → id → list (fexp A) → zexp_aux
| Z_struct_update_base : zexp → struct_name → list (fexp A) → zexp_aux
| Z_struct_update : zexp → struct_name → R → list (id * R) → id → list (fexp A) → zexp_aux

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
  Parameter mk_inline  : annot Tannot.t → t → t.
  Parameter mk_single  : annot Tannot.t → single_case → t → t.
  Parameter mk_var     : annot Tannot.t → zlexp Tannot.t → list t → t → t → t.
  Parameter mk_assign  : annot Tannot.t → zlexp Tannot.t → list t → t → t.
  Parameter mk_undef   : annot Tannot.t → t.
  Parameter mk_struct  : annot Tannot.t → struct_name → list (id * t) → t.
  Parameter mk_struct_update : annot Tannot.t → struct_name → t → list (id * t) → t.
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
  Definition mk_inline  (_ : annot Tannot.t) (_ : t) := tt.
  Definition mk_single  (_ : annot Tannot.t) (_ : single_case) (_ : t) := tt.
  Definition mk_var     (_ : annot Tannot.t) (_ : zlexp Tannot.t) (_ : list t) (_ : t) (_ : t) := tt.
  Definition mk_assign  (_ : annot Tannot.t) (_ : zlexp Tannot.t) (_ : list t) (_ : t) := tt.
  Definition mk_undef   (_ : annot Tannot.t) := tt.
  Definition mk_struct  (_ : annot Tannot.t) (_ : struct_name) (_ : list (id * t)) := tt.
  Definition mk_struct_update (_ : annot Tannot.t) (_ : struct_name) (_ : t) (_ : list (id * t)) := tt.
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
    | Bitvector => E_aux (E_vector (List.rev xs)) ann
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

  Definition mk_inline (ann : annot Tannot.t) (x : t) :=
    let '(loc, tannot) := ann in
    E_aux (E_block [x]) (loc, Tannot.annotate loc "inline" tannot).

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

  Definition mk_fexp (ann : annot Tannot.t) (kv : id * t) : fexp Tannot.t :=
    let '(k, v) := kv in FE_aux (FE_fexp k v) ann.

  Definition mk_struct (ann : annot Tannot.t) (sn : struct_name) (fs : list (id * t)) : t :=
    E_aux (E_struct sn (List.map (mk_fexp ann) (List.rev fs))) ann.

  Definition mk_struct_update (ann : annot Tannot.t) (sn : struct_name) (base : t) (fs : list (id * t)) : t :=
    E_aux (E_struct_update base (List.map (mk_fexp ann) (List.rev fs))) ann.
End ExpBuilder.

Module Residual (Tannot : TypeAnnot.S) (B : Builder Tannot).
  Module L := AbsValue.Dom Interval.Dom AbsBitvector.Dom TransferBitvectorInterval.Ops.

  Module Matching := L.Matching Tannot.

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
      locals    : list (IdMap.t L.t);
      registers : IdMap.t L.t;
    }.

  Definition t : Set := value * B.t.

  Definition is_unit (v : value) : bool :=
    option_is L.is_unit (this v) && is_none (exn v) && negb (eff v).

  (* [is_true] / [is_false] don't gate on [eff]: the partial evaluator runs
     side effects eagerly (writes update state in place, prints go straight
     to stdout), so by the time we're inspecting the value all the effects
     have already happened. If the value is concretely a [bool], we can pick
     the matching branch even if the producing expression was effectful. *)
  Definition is_true (v : value) : bool :=
    option_is L.is_true (this v) && is_none (exn v).

  Definition is_false (v : value) : bool :=
    option_is L.is_false (this v) && is_none (exn v).

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
      | Bitvector => L.mk_bitvector
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
    | Cons =>
        (* [hd :: tl] — when both [hd]'s value and [tl]'s value (which must
           be a [V_list]) are known, produce the concrete [V_list]; otherwise
           lose the value information rather than yielding a spurious one. *)
        let this' :=
          match this (fst x), this (fst y) with
          | Some h, Some (L.V_list ts) => Some (L.V_list (h :: ts))
          | _, _ => ⊥
          end
        in
        ({| this := this'; exn := ⊥; eff := false |}, b)
    end.

  Definition mk_ref (ann : annot Tannot.t) (id : Ast.id) :=
    ({| this := Some (L.V_ref (Aux.unwrap id)); exn := ⊥; eff := false |}, B.mk_ref ann id).

  Definition mk_return (ann : annot Tannot.t) (r : t) :=
    ({| this := ⊥; exn := exn (fst r); eff := true |}, B.mk_return ann (snd r)).

  (* Join a value returned early from an inlined body into the accumulator
     carried on the enclosing [Z_inline] node. *)
  Definition join_returns (acc : option t) (ret : t) : t :=
    match acc with
    | None => ret
    | Some a =>
        ({| this := this (fst a) ⊔ this (fst ret);
            exn  := exn (fst a) ⊔ exn (fst ret);
            eff  := eff (fst a) || eff (fst ret) |}, snd ret)
    end.

  (* [acc] is the join of every value the inlined body [return]ed early, and [r]
     is the value it fell through with. The inlined expression's value is the
     join of the two, so a body all of whose paths return early still yields the
     joined return value rather than [⊥]. *)
  Definition mk_inline (ann : annot Tannot.t) (acc : option t) (r : t) :=
    let this' := match acc with None => this (fst r) | Some a => this (fst a) ⊔ this (fst r) end in
    ({| this := this'; exn := exn (fst r); eff := false |}, B.mk_inline ann (snd r)).

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

  (** Build a [V_record] abstract value out of the (reverse) list of evaluated
      (field, residual) pairs. We join the [exn] and [eff] flags across the
      fields, and collapse [this] into a single [V_record] only when every
      field has a known [this] value (otherwise we propagate [None]). *)
  Definition mk_struct (ann : annot Tannot.t) (sn : struct_name) (rs : list (id * t)) : t :=
    let this_v :=
      List.fold_left
        (fun acc kv =>
          match acc with
          | None => None
          | Some m =>
              let '(k, v) := kv in
              match this (fst v) with
              | None => None
              | Some x => Some (insert (Aux.unwrap k) x m)
              end
          end)
        rs (Some empty) in
    ({|
       this := option_map L.V_record this_v;
       exn := List.fold_left bounded_join (List.map (fun kv => exn (fst (snd kv))) rs) ⊥;
       eff := List.fold_left orb (List.map (fun kv => eff (fst (snd kv))) rs) false;
     |},
     B.mk_struct ann sn (List.map (fun kv => let '(k, v) := kv in (k, snd v)) rs)).

  (** Build a [V_record] update from a base value and a list of field
      (re)assignments. If every field has a known [this] and the base also
      has a known [V_record], we [insert] each new (or replaced) field into
      the base map. Otherwise we conservatively return [None]. *)
  Definition mk_struct_update (ann : annot Tannot.t) (sn : struct_name) (base : t) (rs : list (id * t)) : t :=
    let updated :=
      match this (fst base) with
      | Some (L.V_record base_m) =>
          List.fold_left
            (fun acc kv =>
              match acc with
              | None => None
              | Some m =>
                  let '(k, v) := kv in
                  match this (fst v) with
                  | None => None
                  | Some x => Some (insert (Aux.unwrap k) x m)
                  end
              end)
            rs (Some base_m)
      | _ => None
      end in
    ({|
       this := option_map L.V_record updated;
       exn := List.fold_left bounded_join (List.map (fun kv => exn (fst (snd kv))) rs) (exn (fst base));
       eff := List.fold_left orb (List.map (fun kv => eff (fst (snd kv))) rs) (eff (fst base));
     |},
     B.mk_struct_update ann sn (snd base) (List.map (fun kv => let '(k, v) := kv in (k, snd v)) rs)).

  Definition empty : state := {| locals := [IdMap.empty L.t]; registers := IdMap.empty L.t |}.

  Definition join (σ₁ σ₂ : state) : state := {|
      locals := zip_with (IdMap.map2 bounded_join) (locals σ₁) (locals σ₂);
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
    | ⊥ =>
        match c with
        (* For [try { e } catch { ... }], an absent exception value means
           the body completed normally — no catch arm fires. Report
           [Unmatched] so the match loop falls through cleanly to the
           head's value via [mk_match]'s [is_none (exn _)] branch. *)
        | Try => inr PatternMatch.Unmatched
        | _ => inl l
        end
    | Some v => inr (Matching.pattern_match pat v)
    end.

  (** Joining states leaving a match. We at least need to preserve the
      pre-match state so locals introduced before the match survive into
      the residual evaluation. For the per-arm states we take the lattice
      join across all arms (and the fall-through, if any). *)
  Definition end_match (_ : match_case) (fallthrough : option state) (arms : list state) : state :=
    let arms := match fallthrough with None => arms | Some σ => σ :: arms end in
    match arms with
    | [] => empty
    | σ :: rest => List.fold_left join rest σ
    end.

  (** Push a fresh locals frame when entering a function body, so the
      callee's mutable variables shadow (rather than clobber) any caller
      variables with the same names. *)
  Definition push_scope (σ : state) : state :=
    {| locals := IdMap.empty L.t :: locals σ; registers := registers σ |}.

  (** Pop the callee's locals frame when leaving a function body, discarding
      its mutable variables. The bottom (global) frame is never popped, so an
      unbalanced pop is a no-op rather than leaving future writes with no
      frame to land in. *)
  Definition pop_scope (σ : state) : state :=
    match locals σ with
    | _ :: ((_ :: _) as rest) => {| locals := rest; registers := registers σ |}
    | _ => σ
    end.

  Fixpoint lookup_local (l : Ast.loc) (locals : list (IdMap.t L.t)) (id : Ast.id) {struct locals} : option L.t :=
    match locals with
    | [] => None
    | (top :: stack) =>
        match IdMap.find id top with
        | Some v => Some v
        | None => lookup_local l stack id
        end
    end.

  Definition lookup (l : Ast.loc) (σ : state) (id : Ast.id) : Ast.loc + L.t :=
    match lookup_local l (locals σ) id with
    | Some v => inr v
    | ⊥ =>
        match IdMap.find id (registers σ) with
        | Some v => inr v
        | ⊥ => inl l
        end
    end.

  (** Steps in a path of updates applied while assigning to a structured
      l-value. [US_field] descends through a [V_record], [US_index] through a
      [V_vector] at a concrete index, [US_range] replaces a bitvector subrange
      [lo..hi] (inclusive). Each step's offsets / indices are concretised at
      [zlexp_path] time, so [apply_path] operates on plain [Z]. *)
  Inductive update_step :=
  | US_field : Ast.id_aux → update_step
  | US_index : Z → update_step
  | US_range : Z → Z → update_step.

  (** Apply a left-to-right sequence of updates to [base], replacing the
      target with [v]. Each level reads the current sub-value, recurses, and
      writes the updated sub-value back. *)
  Fixpoint apply_path (base : L.t) (path : list update_step) (v : L.t) : L.t :=
    match path with
    | [] => v
    | step :: rest =>
        match step with
        | US_field k =>
            (* When the field isn't already present (uninitialised base, or
               base is [V_top]), descend into [L.top] rather than [⊥] so a
               freshly-written nested field still produces a recognisable
               nested record. *)
            let child :=
              match base with
              | L.V_record m => match m !! k with Some x => x | None => L.top end
              | _ => L.top
              end in
            L.set_field base k (apply_path child rest v)
        | US_index i => L.set_vector_elem base i (apply_path (L.get_vector_elem base i) rest v)
        | US_range hi lo => L.set_bv_range base hi lo (apply_path L.top rest v)
        end
    end.

  (** Helper: pull a concrete integer out of an evaluated sub-expression. *)
  Definition subexp_concrete_z (r : t) : option Z :=
    match this (fst r) with
    | Some (L.V_int i) => L.int_concrete i
    | _ => None
    end.

  (** Walk a [zlexp] structurally and try to collapse it into a [(root id,
      path of update_steps, leftover sub-expressions)] triple. Returns
      [None] for shapes that don't have a single root id (tuple,
      vector_concat, app, deref) or that include an index / bound we can't
      pin down to a concrete [Z]. *)
  Fixpoint zlexp_path (zl : zlexp Tannot.t) (subexps : list t)
                    : option (Ast.id * list update_step * list t) :=
    let 'LZ_aux aux _ := zl in
    match aux with
    | LZ_id id => Some (id, [], subexps)
    | LZ_typ _ id => Some (id, [], subexps)
    | LZ_deref =>
        (* [*p = e] — the first evaluated sub-expression is [p]. If it
           resolved to a known [V_ref reg_id] we route the rest of the path
           through that register, otherwise we give up. *)
        match subexps with
        | r :: rest =>
            match this (fst r) with
            | Some (L.V_ref reg_id) => Some (Ast.Id_aux reg_id Ast.ext_unknown_loc, [], rest)
            | _ => None
            end
        | [] => None
        end
    | LZ_field inner field =>
        match zlexp_path inner subexps with
        | Some (id, path, rest) => Some (id, path ++ [US_field (Aux.unwrap field)], rest)
        | None => None
        end
    | LZ_vector inner =>
        match zlexp_path inner subexps with
        | Some (id, path, n :: rest) =>
            match subexp_concrete_z n with
            | Some idx => Some (id, path ++ [US_index idx], rest)
            | None => None
            end
        | _ => None
        end
    | LZ_vector_range inner =>
        match zlexp_path inner subexps with
        | Some (id, path, hi :: lo :: rest) =>
            match subexp_concrete_z hi, subexp_concrete_z lo with
            | Some h, Some l => Some (id, path ++ [US_range h l], rest)
            | _, _ => None
            end
        | _ => None
        end
    | _ => None
    end.

  (** Lookup an identifier in [σ], falling through locals → registers → top. *)
  Definition state_lookup (σ : state) (id : Ast.id) : L.t :=
    match lookup ext_unknown_loc σ id with
    | inl _ => L.top
    | inr v => v
    end.

  Definition assign_id (id : Ast.id) (new_v : L.t) (σ : state) : state :=
    match locals σ with
    | [] =>
          {| locals := []; registers := IdMap.add id new_v (registers σ) |}
    | top :: stack =>
        if IdMap.mem id (registers σ) then
          {| locals := locals σ; registers := IdMap.add id new_v (registers σ) |}
        else
          {| locals := IdMap.add id new_v top :: stack; registers := registers σ |}
    end.

  (** Handle a single-rooted l-expression: resolve to (id, path, leftover),
      read the current root value, apply the path, write it back. *)
  Definition assign_via_path (zl : zlexp Tannot.t) (rs : list t) (v : L.t) (σ : state) : state :=
    match zlexp_path zl rs with
    | Some (id, path, _) =>
        match path with
        | [] => assign_id id v σ
        | _ => assign_id id (apply_path (state_lookup σ id) path v) σ
        end
    | None => σ
    end.

  (** Handle [var x = e; ...], [x = e], [x.f = e] (incl. nested), [*p = e]
      (when [p] resolves to a known [V_ref]), [v[i] = e] / [v[hi..lo] = e]
      with concrete bounds, and [(x, (y, z), ...) = e] (incl. nested tuples)
      when the RHS is a known [V_tuple]. For everything else we leave [σ]
      unchanged — the residual still records the write, but downstream reads
      of the same name will see the previous value. *)
  (** Width of the bitvector slice that a single sub-lexp of a
      [LZ_vector_concat] covers. We recover it from the [US_range] step a
      [LZ_vector_range] inner-lexp leaves at the end of its path; sub-lexps
      that aren't range-typed (plain id targets) currently don't have a
      width available without consulting the type annotation, so we report
      [None] and the surrounding assign falls back to a no-op. *)
  Fixpoint last_update_step (path : list update_step) : option update_step :=
    match path with
    | [] => None
    | [s] => Some s
    | _ :: rest => last_update_step rest
    end.

  Definition zlexp_subwidth (zl : zlexp Tannot.t) (subexps : list t) : option Z :=
    match zlexp_path zl subexps with
    | Some (_, path, _) =>
        match last_update_step path with
        | Some (US_range hi lo) => Some (hi - lo + 1)%Z
        | _ => None
        end
    | None => None
    end.

  (** Core of [assign], recursing structurally on the l-expression so nested
      tuple targets like [(x, ((y, z), w)) = e] assign at every depth when the
      corresponding right-hand side value is a known [V_tuple]. Returns the
      updated state together with the sub-expressions left over once this
      l-expression has consumed its share of [rs]. *)
  Fixpoint assign_value (zl : zlexp Tannot.t) (rs : list t) (v : L.t) (σ : state) {struct zl} : state * list t :=
    let 'LZ_aux aux _ := zl in
    match aux with
    | LZ_tuple ls =>
        match v with
        | L.V_tuple vs =>
            (* Walk [ls] and [vs] in lockstep, threading [σ] / leftover
               [rs], recursing into each sub-lexp so nested tuples are
               handled too. *)
            (fix go ls vs rs σ {struct ls} : state * list t :=
               match ls, vs with
               | [], _ => (σ, rs)
               | _, [] => (σ, rs)
               | l :: ls', v :: vs' =>
                   let '(σ', rs') := assign_value l rs v σ in
                   go ls' vs' rs' σ'
               end) ls vs rs σ
        | _ => (σ, rs)
        end
    | LZ_vector_concat ls =>
        (* [(a @ b @ c) = rhs] — split [rhs] by each sub-lexp's width and
           recurse. For [Order dec], the leftmost sub-lexp gets the high
           bits. We track a running offset from the high end ([cur_hi])
           so each sub-lexp gets bits [cur_hi-width+1 .. cur_hi].

           Only handled when every sub-lexp resolves to a concrete-width
           range write (typical of bitfield setters). Anything else degrades
           to a no-op. *)
        match v with
        | L.V_bitvector _ =>
            match L.value_length v with
            | L.V_int i =>
            match L.int_concrete i with
            | Some total =>
                (fix go ls rs cur_hi σ {struct ls} : state * list t :=
                   match ls with
                   | [] => (σ, rs)
                   | l :: ls' =>
                       match zlexp_subwidth l rs with
                       | Some w =>
                           let lo := (cur_hi + 1 - w)%Z in
                           let sliced := L.bv_slice v (Z.to_N lo) (Z.to_N w) in
                           let σ' := assign_via_path l rs sliced σ in
                           let rs' :=
                             match zlexp_path l rs with
                             | Some (_, _, leftover) => leftover
                             | None => rs
                             end in
                           go ls' rs' (cur_hi - w)%Z σ'
                       | None => (σ, rs)
                       end
                   end) ls rs (total - 1)%Z σ
            | None => (σ, rs)
            end
            | _ => (σ, rs)
            end
        | _ => (σ, rs)
        end
    | _ =>
        (* Single-rooted l-expression: resolve to (id, path, leftover), apply
           the path, and report the leftover sub-expressions so tuple targets
           above us keep [rs] in sync. *)
        match zlexp_path zl rs with
        | Some (id, path, leftover) =>
            let σ' :=
              match path with
              | [] => assign_id id v σ
              | _ => assign_id id (apply_path (state_lookup σ id) path v) σ
              end in
            (σ', leftover)
        | None => (σ, rs)
        end
    end.

  Definition assign (zl : zlexp Tannot.t) (rs : list t) (exp : t) (σ : state) : state :=
    let v := match this (fst exp) with Some v => v | None => L.top end in
    fst (assign_value zl rs v σ).
End Residual.

Module Make (Tannot : TypeAnnot.S) (B : Builder Tannot).
  Module R := Residual Tannot B.
  Module L := R.L.

  (* TODO: Find a way to share the monad with Semantics.v *)
  Module Monad.
    Inductive function_return : Type :=
    | Return_inlined : list (pat Tannot.t * option (exp Tannot.t) * exp Tannot.t) → function_return
    | Return_value : R.value → function_return.

    Inductive t {A : Type} : Type :=
    | Pure : A → t
    | Early_return : R.value → (unit → t) → t
    | Exit : R.value → (unit → t) → t
    | Call : id → list R.value → (function_return → t) → t
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
      | Z_var_body parent _ _ _
      | Z_struct parent _ _ _ _
      | Z_struct_update_base parent _ _
      | Z_struct_update parent _ _ _ _ _ => lookup parent id

      (* Stop at an inlined function boundary. *)
      | Z_inline _ _ => None

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
            match Tannot.get_id_type (snd annot) i with
            | TypeAnnot.Types.Enum_member =>
                pure (ctx, σ, inr (R.from_semilattice (L.mk_member (IdUtil.Aux.unwrap i)), B.mk_id annot i))
            | _ =>
                v ← Monad.lift_sum (R.lookup (fst annot) σ i);
                pure (ctx, σ, inr (R.from_semilattice v, B.mk_id annot i))
            end
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
            ret ← Monad.Call f [] pure;
            match ret with
            | Monad.Return_value r => pure (ctx, σ, inr (r, B.mk_app annot f []))
            | Monad.Return_inlined arms =>
                pure (Z_aux (Z_match_head (Z_aux (Z_inline ctx None) annot) Match [] (Some arms)) annot, R.push_scope σ, inr (R.from_semilattice L.V_unit, B.mk_literal annot (L_aux L_unit (fst annot))))
            end
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
        | exp :: exps =>
            if Tannot.is_bitvector (snd annot) then
              wrap (Z_list ctx Bitvector [] exps) exp
            else
              wrap (Z_list ctx Vector [] exps) exp
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

    | E_struct sn fes =>
        match fes with
        | [] => pure (ctx, σ, inr (R.mk_struct annot sn []))
        | FE_aux (FE_fexp f e) _ :: rest => wrap (Z_struct ctx sn [] f rest) e
        end

    | E_struct_update base fes => wrap (Z_struct_update_base ctx SN_anon fes) base

    | E_for _ _ _ _ _ _ | E_loop _ _ _ _ => Monad.Runtime_type_error (fst annot)

    | E_sizeof _ | E_constraint _ | E_internal_value _ => Monad.Runtime_type_error (fst annot)
    end.

  (* When a [return] fires inside an inlined function body its value must be
     joined into the accumulator carried by the nearest enclosing [Z_inline]
     marker, rather than escaping the whole computation (as it would for a real
     call handled via [Early_return]). This walks up the zipper, rebuilding the
     intervening spine, and joins [ret] into that accumulator. It returns [None]
     when there is no enclosing [Z_inline] — i.e. we are not inside an inlined
     body — so the caller can fall back to the [Early_return] mechanism. *)
  Fixpoint join_inline_return (ret : R.t) (ctx : t) : option t :=
    match ctx with
    | Z_top => None
    | Z_aux aux annot =>
      match aux with
      | Z_inline parent acc =>
          Some (Z_aux (Z_inline parent (Some (R.join_returns acc ret))) annot)
      | Z_single parent c =>
          option_map (fun p => Z_aux (Z_single p c) annot) (join_inline_return ret parent)
      | Z_return parent =>
          option_map (fun p => Z_aux (Z_return p) annot) (join_inline_return ret parent)
      | Z_exit parent =>
          option_map (fun p => Z_aux (Z_exit p) annot) (join_inline_return ret parent)
      | Z_pair_1 parent c e =>
          option_map (fun p => Z_aux (Z_pair_1 p c e) annot) (join_inline_return ret parent)
      | Z_pair_2 parent c r =>
          option_map (fun p => Z_aux (Z_pair_2 p c r) annot) (join_inline_return ret parent)
      | Z_list parent c rs es =>
          option_map (fun p => Z_aux (Z_list p c rs es) annot) (join_inline_return ret parent)
      | Z_app parent f rs es =>
          option_map (fun p => Z_aux (Z_app p f rs es) annot) (join_inline_return ret parent)
      | Z_block parent rs es =>
          option_map (fun p => Z_aux (Z_block p rs es) annot) (join_inline_return ret parent)
      | Z_if_cond parent thn els =>
          option_map (fun p => Z_aux (Z_if_cond p thn els) annot) (join_inline_return ret parent)
      | Z_if_then parent sr els =>
          option_map (fun p => Z_aux (Z_if_then p sr els) annot) (join_inline_return ret parent)
      | Z_if_else parent thn sr =>
          option_map (fun p => Z_aux (Z_if_else p thn sr) annot) (join_inline_return ret parent)
      | Z_match_head parent mc ev un =>
          option_map (fun p => Z_aux (Z_match_head p mc ev un) annot) (join_inline_return ret parent)
      | Z_match_arms_guard parent mc bnd sr ev pt gm bd un =>
          option_map (fun p => Z_aux (Z_match_arms_guard p mc bnd sr ev pt gm bd un) annot) (join_inline_return ret parent)
      | Z_match_arms_body parent mc bnd sr ev pt gd un =>
          option_map (fun p => Z_aux (Z_match_arms_body p mc bnd sr ev pt gd un) annot) (join_inline_return ret parent)
      | Z_assign_left parent l rs es e =>
          option_map (fun p => Z_aux (Z_assign_left p l rs es e) annot) (join_inline_return ret parent)
      | Z_assign_right parent l rs =>
          option_map (fun p => Z_aux (Z_assign_right p l rs) annot) (join_inline_return ret parent)
      | Z_var_left parent l rs es e1 e2 =>
          option_map (fun p => Z_aux (Z_var_left p l rs es e1 e2) annot) (join_inline_return ret parent)
      | Z_var_right parent l rs e =>
          option_map (fun p => Z_aux (Z_var_right p l rs e) annot) (join_inline_return ret parent)
      | Z_var_body parent l rs r =>
          option_map (fun p => Z_aux (Z_var_body p l rs r) annot) (join_inline_return ret parent)
      | Z_struct parent sn rs f fes =>
          option_map (fun p => Z_aux (Z_struct p sn rs f fes) annot) (join_inline_return ret parent)
      | Z_struct_update_base parent sn fes =>
          option_map (fun p => Z_aux (Z_struct_update_base p sn fes) annot) (join_inline_return ret parent)
      | Z_struct_update parent sn r rs f fes =>
          option_map (fun p => Z_aux (Z_struct_update p sn r rs f fes) annot) (join_inline_return ret parent)
      end
    end.

  Definition next (aux : zexp_aux (IdMap.t L.t) R.t R.state Tannot.t)
                  (annot : annot Tannot.t)
                  (σ : R.state)
                  (focus : R.t)
                : Monad.t (t * R.state * (exp Tannot.t + R.t)) :=
    match aux with
    | Z_if_cond parent t e =>
        if R.is_true (fst focus) then
          pure (Z_aux (Z_block parent [focus] []) annot, σ, inl t)
        else if R.is_false (fst focus) then
          pure (Z_aux (Z_block parent [focus] []) annot, σ, inl e)
        else
          pure (Z_aux (Z_if_then parent (σ, focus) e) annot, σ, inl t)
    | Z_if_then parent (σ_i, i) e =>
        pure (Z_aux (Z_if_else parent i (σ, focus)) annot, σ_i, inl e)
    | Z_if_else parent i (σ_t, t) =>
        pure (parent, R.join σ_t σ, inr (R.mk_ite annot i t focus))

    | Z_single parent γ =>
        pure (parent, σ, inr (R.mk_single annot γ focus))

    | Z_return parent =>
        (* If we are inside an inlined function body, join the returned value
           into the enclosing [Z_inline] and continue evaluating (so returns in
           other speculative branches are also accounted for). *)
        match join_inline_return focus parent with
        | Some parent' => pure (parent', σ, inr (R.mk_return annot focus))
        | None =>
            _ ← Monad.Early_return (fst focus) pure;
            pure (parent, σ, inr (R.mk_return annot focus))
        end

    | Z_inline parent acc =>
        pure (parent, R.pop_scope σ, inr (R.mk_inline annot acc focus))

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
        (* If [focus] has [this = ⊥] we've just evaluated a statement that
           diverges on every path — a [throw e], an early [return] (in an
           inlined body), or an [exit] — so the rest of the block is
           unreachable. Stop here and surface [focus] as the block's value; an
           enclosing [try]/[Z_match_head Try _ _ _] will pick up any [exn], and
           an enclosing [Z_inline] will already hold the returned value. *)
        match unevaluated with
        | []      => pure (parent, σ, inr (R.mk_block annot (focus :: evaluated)))
        | u :: us =>
            if is_none (R.this (fst focus)) then
              pure (parent, σ, inr focus)
            else if R.is_unit (fst focus) then
              pure (Z_aux (Z_block parent evaluated us) annot, σ, inl u)
            else
              pure (Z_aux (Z_block parent (focus :: evaluated) us) annot, σ, inl u)
        end

    | Z_app parent f evaluated unevaluated =>
        match f, evaluated, unevaluated with
        (* [and_bool(a, b)] and [or_bool(a, b)] are short-circuit operators
           in Sail. Once [a] has been evaluated we hand control off to the
           [Z_if_then] machinery, which both folds statically-known cases
           (avoiding evaluating [b] when [a] determines the result) and, in
           the dynamic case, produces an [if-then-else] residual instead of
           an [and_bool]/[or_bool] call:
             [a & b]  ≡  if a then b    else false
             [a | b]  ≡  if a then true else b      *)
        | Ast.Id_aux Ast.And_bool _, [], b :: nil =>
            let false_lit : exp Tannot.t :=
              E_aux (E_lit (L_aux L_false Ast.ext_unknown_loc)) annot in
            if R.is_true (fst focus) then
              pure (parent, σ, inl b)
            else if R.is_false (fst focus) then
              pure (parent, σ, inr focus)
            else
              pure (Z_aux (Z_if_then parent (σ, focus) false_lit) annot, σ, inl b)
        | Ast.Id_aux Ast.Or_bool _, [], b :: nil =>
            let true_lit : exp Tannot.t :=
              E_aux (E_lit (L_aux L_true Ast.ext_unknown_loc)) annot in
            if R.is_true (fst focus) then
              pure (parent, σ, inr focus)
            else if R.is_false (fst focus) then
              pure (parent, σ, inl b)
            else
              pure (Z_aux (Z_if_then parent (σ, focus) b) annot, σ, inl true_lit)
        | _, _, [] =>
            ret ← Monad.Call f (List.rev (List.map fst (focus :: evaluated))) pure;
            match ret with
            | Monad.Return_value r =>
                pure (parent, σ, inr (r, B.mk_app annot f (List.rev (List.map snd (focus :: evaluated)))))
            | Monad.Return_inlined arms =>
                match evaluated with
                | [] =>
                    pure (Z_aux (Z_match_head (Z_aux (Z_inline parent None) annot) Match [] (Some arms)) annot, R.push_scope σ, inr focus)
                | _ =>
                    pure (Z_aux (Z_match_head (Z_aux (Z_inline parent None) annot) Match [] (Some arms)) annot, R.push_scope σ, inr (R.mk_list annot Tuple (focus :: evaluated)))
                end
            end
        | _, _, u :: us => pure (Z_aux (Z_app parent f (focus :: evaluated) us) annot, σ, inl u)
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
                    (* Even though the pattern is a guaranteed match, the
                       guard can still fail at runtime, so we keep the
                       remaining arms as fall-back. The [true] flag
                       ([guaranteed_match]) tells the guard handler to drop
                       them iff the guard evaluates to [true]. *)
                    pure (Z_aux (Z_match_arms_guard parent γ β (σ, focus) evaluated pat true body (Some arms)) annot, σ, inl g)
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
        if andb (is_none (R.this (fst focus))) (negb (is_none (R.exn (fst focus)))) then
          (* The guard threw an exception. Its body never runs, and the
             remaining arms aren't tried either — the exception escapes the
             enclosing [try]/[match] to be handled (or not) further up. *)
          pure (parent, σ, inr focus)
        else if R.is_true (fst focus) then
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
        | [] => pure (Z_aux (Z_assign_right parent l (List.rev (focus :: evaluated))) annot, σ, inl exp)
        | u :: us => pure (Z_aux (Z_assign_left parent l (focus :: evaluated) us exp) annot, σ, inl u)
        end
    | Z_assign_right parent l evaluated =>
        pure (parent, R.assign l evaluated focus σ, inr (R.mk_assign annot l evaluated focus))

    | Z_var_left parent l evaluated unevaluated exp body =>
        match unevaluated with
        | [] => pure (Z_aux (Z_var_right parent l (List.rev (focus :: evaluated)) body) annot, σ, inl exp)
        | u :: us => pure (Z_aux (Z_var_left parent l (focus :: evaluated) us exp body) annot, σ, inl u)
        end
    | Z_var_right parent l evaluated body =>
        pure (Z_aux (Z_var_body parent l evaluated focus) annot, R.assign l evaluated focus σ, inl body)
    | Z_var_body parent l evaluated v =>
        pure (parent, σ, inr (R.mk_var annot l evaluated v focus))

    | Z_struct parent sn evaluated cur unevaluated =>
        let evaluated' := (cur, focus) :: evaluated in
        match unevaluated with
        | [] => pure (parent, σ, inr (R.mk_struct annot sn evaluated'))
        | FE_aux (FE_fexp f e) _ :: rest =>
            pure (Z_aux (Z_struct parent sn evaluated' f rest) annot, σ, inl e)
        end

    | Z_struct_update_base parent sn fes =>
        match fes with
        | [] => pure (parent, σ, inr (R.mk_struct_update annot sn focus []))
        | FE_aux (FE_fexp f e) _ :: rest =>
            pure (Z_aux (Z_struct_update parent sn focus [] f rest) annot, σ, inl e)
        end

    | Z_struct_update parent sn base evaluated cur unevaluated =>
        let evaluated' := (cur, focus) :: evaluated in
        match unevaluated with
        | [] => pure (parent, σ, inr (R.mk_struct_update annot sn base evaluated'))
        | FE_aux (FE_fexp f e) _ :: rest =>
            pure (Z_aux (Z_struct_update parent sn base evaluated' f rest) annot, σ, inl e)
        end
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
