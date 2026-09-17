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

(** * Vector primitives

    Concrete definitions of the Sail primitives that operate on generic
    vectors. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.

Import ListNotations.

Open Scope Z_scope.

Fixpoint take {A} (n : Z) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs => if Z.leb n 0 then [] else x :: take (n - 1) xs
  end.

Fixpoint drop {A} (n : Z) (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => if Z.leb n 0 then x :: xs' else drop (n - 1) xs'
  end.

Lemma take_drop_app : forall {A} (n : Z) (xs : list A), take n xs ++ drop n xs = xs.
Proof.
  intros A n xs; revert n.
  induction xs as [| x xs IH]; intro n; cbn.
  - reflexivity.
  - destruct (Z.leb n 0); cbn.
    + reflexivity.
    + rewrite IH; reflexivity.
Qed.

Definition append {A} (xs ys : list A) : list A := xs ++ ys.

Fixpoint length {A} (xs : list A) : Z :=
  match xs with
  | [] => 0
  | _ :: xs => Z.succ (length xs)
  end.

Lemma length_of_nat : forall {A} (xs : list A), length xs = Z.of_nat (List.length xs).
Proof.
  intros A xs; induction xs as [| x xs IH]; [reflexivity |].
  cbn [length Datatypes.length].
  rewrite IH, Nat2Z.inj_succ.
  reflexivity.
Qed.

Definition vector_init {A} (n : Z) (elem : A) : list A :=
  List.repeat elem (Z.to_nat n).

Lemma vector_init_length : forall {A} n (x : A), 0 <= n -> length (vector_init n x) = n.
Proof.
  intros A n x H.
  unfold vector_init.
  rewrite length_of_nat, List.repeat_length.
  apply Z2Nat.id; assumption.
Qed.

Definition subrange {A} (xs : list A) (n m : Z) : list A :=
  List.rev (take (n - (m - 1)) (drop m (List.rev xs))).

Definition subrange_inc {A} (xs : list A) (n m : Z) : list A :=
  take (m - (n - 1)) (drop n xs).

Definition slice {A} (xs : list A) (n m : Z) : list A :=
  List.rev (take m (drop n (List.rev xs))).

Definition slice_inc {A} (xs : list A) (n m : Z) : list A :=
  take m (drop n xs).

Definition vector_truncate {A} (xs : list A) (n : Z) : list A :=
  List.rev (take n (List.rev xs)).

Definition vector_truncateLSB {A} (xs : list A) (n : Z) : list A := take n xs.

Definition update_list {A} (xs : list A) (n : Z) (x : A) : list A :=
  let i := length xs - n - 1 in
  take i xs ++ [x] ++ drop (i + 1) xs.

Definition update_list_inc {A} (xs : list A) (n : Z) (x : A) : list A :=
  take n xs ++ [x] ++ drop (n + 1) xs.

Definition update {A} (xs : list A) (n : Z) (x : list A) : list A :=
  let i := length xs - n - 1 in
  take i xs ++ x ++ drop (i + 1) xs.

Definition update_inc {A} (xs : list A) (n : Z) (x : list A) : list A :=
  take n xs ++ x ++ drop (n + 1) xs.

Fixpoint update_subrange {A} (xs : list A) (o : Z) (ys : list A) : list A :=
  match ys with
  | [] => xs
  | y :: ys => update_subrange (update_list xs o y) (o - 1) ys
  end.

Fixpoint update_subrange_inc {A} (xs : list A) (o : Z) (ys : list A) : list A :=
  match ys with
  | [] => xs
  | y :: ys => update_subrange_inc (update_list_inc xs o y) (o + 1) ys
  end.

Definition replicate_bits {A} (xs : list A) (n : Z) : list A :=
  List.concat (List.repeat xs (Z.to_nat n)).

Fixpoint reverse_endianness_fuel {A} (fuel : nat) (xs : list A) : list A :=
  match fuel with
  | O => xs
  | S fuel =>
      if Z.leb (length xs) 8 then
        xs
      else
        reverse_endianness_fuel fuel (drop 8 xs) ++ take 8 xs
  end.

Definition reverse_endianness {A} (xs : list A) : list A :=
  reverse_endianness_fuel (List.length xs) xs.

Definition arith_shiftr {A} (xs : list A) (y : Z) : list A :=
  take (length xs) (replicate_bits (take 1 xs) y ++ xs).

Definition access_inc {A} (xs : list A) (n : Z) : list A :=
  if Z.ltb n 0 then
    []
  else
    match List.nth_error xs (Z.to_nat n) with
    | Some x => [x]
    | None => []
    end.

Definition access {A} (xs : list A) (n : Z) : list A :=
  access_inc (List.rev xs) n.
