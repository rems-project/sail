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

From Stdlib Require Import List.

From Sail Require Import Tactics.

Import ListNotations.

Definition is_none {A} (o : option A) : bool := match o with Some _ => false | None => true end.
Definition is_some {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition option_bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition option_map2 {A B C} (f : A -> B -> C) (o₁ : option A) (o₂ : option B) : option C :=
  match (o₁, o₂) with
  | (None, _) => None
  | (_, None) => None
  | (Some x, Some y) => Some (f x y)
  end.

Definition option_join {A} (f : A -> A -> A) (o₁ o₂ : option A) : option A :=
  match (o₁, o₂) with
  | (None, None) => None
  | (Some x, None) => Some x
  | (None, Some y) => Some y
  | (Some x, Some y) => Some (f x y)
  end.

Section option_join.
  Context {A : Type}.
  Context {f : A -> A -> A}.

  Lemma option_join_idem : forall (f_idem : forall x, f x x = x) {x : option A},
    option_join f x x = x.
  Proof using A f.
    intros f_idem x.
    destruct x as [x |]; try reflexivity.
    cbn.
    rewrite f_idem.
    reflexivity.
  Qed.

  Lemma option_join_comm : forall (f_sym : forall x y, f x y = f y x) {x y : option A},
    option_join f x y = option_join f y x.
  Proof using A f.
    intros f_sym x y.
    destruct x as [x |]; destruct y as [y |]; try reflexivity.
    cbn.
    rewrite f_sym.
    reflexivity.
  Qed.

  Lemma option_join_assoc : forall (f_assoc : forall x y z, f (f x y) z = f x (f y z)) {x y z : option A},
    option_join f (option_join f x y) z = option_join f x (option_join f y z).
  Proof using A f.
    intros f_assoc x y z.
    destruct x as [x |]; destruct y as [y |]; destruct z as [z |]; try reflexivity.
    cbn.
    rewrite f_assoc.
    reflexivity.
  Qed.

  Lemma option_join_bounded_r : forall {x : option A}, option_join f x None = x.
  Proof using A f. intros x; destruct x; reflexivity. Qed.

  Lemma option_join_bounded_l : forall {x : option A}, option_join f None x = x.
  Proof using A f. intros x; destruct x; reflexivity. Qed.
End option_join.

(**
[option_all] takes a list of options, and returns [Some list] if all
the items in the list are wrapped in [Some], otherwise [None].

First, a tail-recursive definition of option_all:
*)

Fixpoint option_all' {A} (acc : option (list A)) (xs : list (option A)) : option (list A) :=
  match acc with
  | None => None
  | Some acc =>
      match xs with
      | [] => Some (List.rev acc)
      | None :: _ => None
      | Some x :: xs => option_all' (Some (x :: acc)) xs
      end
  end.

Definition option_all {A} (xs : list (option A)) : option (list A) := option_all' (Some []) xs.

(**
Second, a non tail-recursive definition of option_all that avoids the
accumulator, so likely easier to reason about. We prove them
equivalent ([option_all_is_alt]):
*)

Fixpoint option_all_alt {A} (xs : list (option A)) : option (list A) :=
  match xs with
  | [] => Some []
  | None :: _ => None
  | Some x :: xs =>
      match option_all_alt xs with
      | Some xs => Some (x :: xs)
      | None => None
      end
  end.

Lemma option_all_prime_is_alt : forall {A} {xs : list (option A)} (ys : list A),
  option_all' (Some ys) xs = option_map (fun zs => rev ys ++ zs) (option_all_alt xs).
Proof.
  intros A xs.
  induction xs as [| x xs IHxs]; intros ys.
  - cbn. rewrite app_nil_r. reflexivity.
  - cbn.
    destruct_match; try rewrite IHxs; cbn; try reflexivity.
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma option_all_is_alt : forall {A} {xs : list (option A)}, option_all xs = option_all_alt xs.
Proof.
  intros A xs.
  unfold option_all.
  rewrite (option_all_prime_is_alt []).
  unfold option_map.
  destruct_match; reflexivity.
Qed.

Definition option_is {A} (f : A -> bool) (o : option A) : bool :=
  match o with
  | Some x => f x
  | None   => false
  end.
