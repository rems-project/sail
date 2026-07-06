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

From Stdlib Require Import Lia.

From stdpp Require Import base.

From Sail Require Import Ast.
From Sail Require Import AstInduction.
From Sail Require Import ListUtil.
From Sail Require TypeAnnot.

Import TypeAnnot.Types.

(** * Assignment functions and properties

This file contains various helper functions and properties for working
with L-expressions and assignment statements.
*)

(** ** L-expression subexpressions

Some L-expression forms can contain nested subexpressions. This
function returns them in left-to-right (evaluation) order. *)

Fixpoint lexp_subexps {A : Set} (l : lexp A) : list (exp A) :=
  let 'LE_aux aux _ := l in
  match aux with
  | LE_id _ | LE_typ _ _ => []
  | LE_deref x => [x]
  | LE_tuple ls
  | LE_vector_concat ls =>
      concat (map lexp_subexps ls)
  | LE_vector l x => lexp_subexps l ++ [x]
  | LE_vector_range l n m => lexp_subexps l ++ [n; m]
  | LE_field l _ => lexp_subexps l
  end.

(** Once extracted by [lexp_subexps], this function puts
subexpressions back into an L-expression, replacing the existing
subexpressions. *)

Fixpoint update_lexp_subexps {A : Set} (xs : list (exp A)) (l : lexp A) : lexp A * list (exp A) :=
  let 'LE_aux aux annot := l in
  match aux with
  | LE_id _ | LE_typ _ _ => (l, xs)
  | LE_deref _ =>
      match xs with
      | y :: ys =>
          (LE_aux (LE_deref y) annot, ys)
      | _ => (l, xs)
      end
  | LE_field l f =>
      let '(l', ys) := update_lexp_subexps xs l in
      (LE_aux (LE_field l' f) annot, ys)
  | LE_tuple ls =>
      let '(ls, xs) :=
        fold_left
          (fun acc l =>
             let '(ls, xs) := acc in
             let '(l, xs) := update_lexp_subexps xs l in
             (ls ++ [l], xs)
          )
          ls
          ([], xs)
      in
      (LE_aux (LE_tuple ls) annot, xs)
  | LE_vector_concat ls =>
      let '(ls, xs) :=
        fold_left
          (fun acc l =>
             let '(ls, xs) := acc in
             let '(l, xs) := update_lexp_subexps xs l in
             (ls ++ [l], xs)
          )
          ls
          ([], xs)
      in
      (LE_aux (LE_vector_concat ls) annot, xs)
  | LE_vector l n =>
      match update_lexp_subexps xs l with
      | (l, n :: xs) =>
          (LE_aux (LE_vector l n) annot, xs)
      | _ =>
          (l, [])
      end
  | LE_vector_range l n m =>
      match update_lexp_subexps xs l with
      | (l, n :: m :: xs) =>
          (LE_aux (LE_vector_range l n m) annot, xs)
      | _ =>
          (l, [])
      end
  end.

Definition cons_lexp {A : Set} (lx : lexp A) (acc : lexp A * list (exp A)) : lexp A * list (exp A) :=
  let '(LE_aux aux ann, xs) := acc in
  match aux with
  | (LE_tuple lxs) => (LE_aux (LE_tuple (lx :: lxs)) ann, xs)
  | (LE_vector_concat lxs) => (LE_aux (LE_vector_concat (lx :: lxs)) ann, xs)
  | _ => acc
  end.

Lemma cons_lexp_tuple : ∀ (A : Set) (P : list (lexp A) * list (exp A)) (a : lexp A) ann,
  (let '(ls0, xs) := let '(a0, b) := P in (a :: a0, b) in (LE_aux (LE_tuple ls0) ann, xs))
  = cons_lexp a (let '(a0, b) := P in (LE_aux (LE_tuple a0) ann, b)).
Proof.
  destruct P.
  reflexivity.
Qed.

Lemma cons_lexp_vector_concat : ∀ (A : Set) (P : list (lexp A) * list (exp A)) (a : lexp A) ann,
  (let '(ls0, xs) := let '(a0, b) := P in (a :: a0, b) in (LE_aux (LE_vector_concat ls0) ann, xs))
  = cons_lexp a (let '(a0, b) := P in (LE_aux (LE_vector_concat a0) ann, b)).
Proof.
  destruct P.
  cbn. reflexivity.
Qed.

Lemma lexp_subexps_identity_g : ∀ (A : Set) (l : lexp A) (es : list (exp A)),
  update_lexp_subexps (lexp_subexps l ++ es) l = (l, es).
Proof.
  induction l using lexp_ind_g.
  all: try reflexivity.
  - induction ls.
    + reflexivity.
    + rewrite Forall_cons_iff in H.
      inversion H as [Hhd Htl].
      pose proof (IHls Htl) as Htl2.
      intros.
      cbn.
      rewrite <- app_assoc.
      rewrite Hhd.
      cbn in Htl2.
      rewrite foldl_acc.
      cbn.
      rewrite cons_lexp_tuple.
      rewrite Htl2.
      reflexivity.
  - induction ls.
    + reflexivity.
    + rewrite Forall_cons_iff in H.
      inversion H as [Hhd Htl].
      pose proof (IHls Htl) as Htl2.
      intros.
      cbn.
      rewrite <- app_assoc.
      rewrite Hhd.
      cbn in Htl2.
      rewrite foldl_acc.
      cbn.
      rewrite cons_lexp_vector_concat.
      rewrite Htl2.
      reflexivity.
  - cbn. intros. rewrite <- app_assoc. rewrite IHl. reflexivity.
  - cbn. intros. rewrite <- app_assoc. rewrite IHl. reflexivity.
  - cbn. intros. rewrite IHl. reflexivity.
Qed.

(** The key property is extracting the subexpressions with
[lexp_subexps] then putting them back with [update_lexp_subexps]
returns the original L-expression. *)

Lemma lexp_subexps_identity : ∀ (A : Set) (l : lexp A), update_lexp_subexps (lexp_subexps l) l = (l, []).
Proof.
  intros A l.
  pose proof (lexp_subexps_identity_g A l []) as H.
  rewrite app_nil_r in H.
  assumption.
Qed.

(** ** L-expression depth *)

Lemma lexp_subexps_depth : ∀ (A : Set) (l : lexp A),
  fold_right max 0 (map depth (lexp_subexps l)) ≤ lexp_depth l.
Proof.
   intros.
   induction l using lexp_ind_g.
   - reflexivity.
   - cbn. lia.
   - cbn. lia.
   - induction ls.
     + cbn. lia.
     + cbn.
       cbn in IHls.
       rewrite map_app.
       rewrite Forall_cons_iff in H.
       inversion H.
       apply IHls in H1.
       rewrite fold_max_app.
       lia.
   - induction ls.
     + cbn. lia.
     + cbn.
       cbn in IHls.
       rewrite map_app.
       rewrite Forall_cons_iff in H.
       inversion H.
       apply IHls in H1.
       rewrite fold_max_app.
       lia.
   - cbn.
     rewrite map_app.
     rewrite fold_max_app.
     cbn.
     lia.
   - cbn.
     rewrite map_app.
     rewrite fold_max_app.
     cbn.
     lia.
   - cbn. lia.
Qed.

(** ** L-expressions without embedded subexpressions

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

(** Now, as above, we can prove the key property for the [zlexp] type,
that we can map it to and from an l-expression [l]. *)

Lemma update_zlexp_identity : ∀ {A} (l : lexp A),
  update_zlexp_subexps (lexp_subexps l) (lexp_to_z l) = (Some l, []).
Proof.
  intros A l.
  pose proof (update_zlexp_identity_g l []) as H.
  rewrite app_nil_r in H.
  exact H.
Qed.

(** ** L-expression structure

The type-system of Sail enforces some additional structure on
L-expressions which is not inherent in the [lexp] type.

Specifically, a L-expression consists of an outer destructuring part
that is similar (but more restrictive than) general patterns, and
inner 'places' that represent things that can be assigned to. *)

Inductive var_type : Set :=
| Var_local : var_type
| Var_register : var_type.

Inductive place {V : Set} : Set :=
| PL_id : id → var_type → place
| PL_register : V → place
| PL_vector : place → V → place
| PL_vector_range : place → V → V → place
| PL_field : place → id → place.

Arguments place V : clear implicits.

Inductive destructure {V : Set} : Set :=
| DL_tuple : list destructure → destructure
| DL_vector_concat : list (vector_concat_split * destructure) → destructure
| DL_place : place V → destructure.

Arguments destructure V : clear implicits.

Module Typed (Tannot : TypeAnnot.S).
  Fixpoint zlexp_to_destructure {V : Set} (xs : list V) (l : zlexp Tannot.t) {struct l} : option (destructure V) * list V :=
    let 'LZ_aux aux annot := l in
    match aux with
    | LZ_id var
    | LZ_typ _ var =>
        match Tannot.get_id_type (snd annot) var with
        | Global_register =>
            (Some (DL_place (PL_id var Var_register)), xs)
        | Local_variable =>
            (Some (DL_place (PL_id var Var_local)), xs)
        | Enum_member =>
            (None, xs)
        end
    | LZ_deref =>
        match xs with
        | x :: xs' =>
            (Some (DL_place (PL_register x)), xs')
        | [] => (None, [])
        end
    | LZ_field l fld =>
        match zlexp_to_destructure xs l with
        | (Some (DL_place p), xs) => (Some (DL_place (PL_field p fld)), xs)
        | _ => (None, [])
        end
    | LZ_tuple ls =>
        match fold_left (consume zlexp_to_destructure) ls (Some [], xs) with
        | (Some ds, xs) => (Some (DL_tuple (List.rev ds)), xs)
        | (None, xs) => (None, xs)
        end
    | LZ_vector_concat ls =>
        let widths := map (fun '(LZ_aux _ annot) => Tannot.get_split (snd annot)) ls in
        match fold_left (consume zlexp_to_destructure) ls (Some [], xs) with
        | (Some ds, xs) => (Some (DL_vector_concat (combine widths (List.rev ds))), xs)
        | (None, xs) => (None, xs)
        end
    | LZ_vector l =>
        match zlexp_to_destructure xs l with
        | (Some (DL_place p), n :: xs) => (Some (DL_place (PL_vector p n)), xs)
        | _ => (None, [])
        end
    | LZ_vector_range l =>
        match zlexp_to_destructure xs l with
        | (Some (DL_place p), n :: m :: xs) => (Some (DL_place (PL_vector_range p n m)), xs)
        | _ => (None, [])
        end
    end.
End Typed.
