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


From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import String.

From stdpp Require Import base.

From Sail Require Import Ast.

(**
A monad for executing Sail, shared by the concrete interpreter
([Semantics]) and the partial evaluator ([ZAst]).

The monad is a free monad over the effects that evaluating a Sail
expression can perform. It is parameterized over:

- [V], the type of values, e.g. concrete values for the interpreter,
  or abstract values for the partial evaluator.
- [C], the type returned to the evaluator when a function call
  completes.
- [P], the type of places that can be read and written with
  [Read_var] and [Write_var].

Not every client uses every effect. The partial evaluator, for
example, does not use [Read_var] or [Write_var] as it tracks variable
state itself.
*)

Inductive t (V C P A : Type) : Type :=
| Pure : A → t V C P A
| Early_return : V → t V C P A
| Exit : V → t V C P A
| Exception : V → t V C P A
| Runtime_type_error : Ast.loc → t V C P A
| Match_failure : Ast.loc → t V C P A
| Assertion_failed : string → t V C P A
| Call : id → list V → (C → t V C P A) → t V C P A
| Read_var : P → (V → t V C P A) → t V C P A
| Write_var : P → V → (unit → t V C P A) → t V C P A
| Get_config : Ast.loc → list string → typ → (V → t V C P A) → t V C P A
| Get_undefined : Ast.loc → typ → (V → t V C P A) → t V C P A.

Arguments Pure {_ _ _ _}.
Arguments Early_return {_ _ _ _}.
Arguments Exit {_ _ _ _}.
Arguments Exception {_ _ _ _}.
Arguments Runtime_type_error {_ _ _ _}.
Arguments Match_failure {_ _ _ _}.
Arguments Assertion_failed {_ _ _ _}.
Arguments Call {_ _ _ _}.
Arguments Read_var {_ _ _ _}.
Arguments Write_var {_ _ _ _}.
Arguments Get_config {_ _ _ _}.
Arguments Get_undefined {_ _ _ _}.

Section Monad.
  Context {V C P : Type}.

  Local Notation M := (t V C P).

  Fixpoint bind {A B : Type} (m : M A) (f : A → M B) : M B :=
    match m with
    | Pure x => f x
    | Early_return v => Early_return v
    | Exit v => Exit v
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => bind (cont v) f)
    | Read_var r cont => Read_var r (fun v => bind (cont v) f)
    | Write_var r v cont => Write_var r v (fun u => bind (cont u) f)
    | Get_config l key t cont => Get_config l key t (fun v => bind (cont v) f)
    | Get_undefined l t cont => Get_undefined l t (fun v => bind (cont v) f)
    end.

  Fixpoint fmap {A B : Type} (f : A → B) (m : M A) : M B :=
    match m with
    | Pure x => Pure (f x)
    | Early_return v => Early_return v
    | Exit v => Exit v
    | Exception v => Exception v
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap f (cont v))
    | Read_var r cont => Read_var r (fun v => fmap f (cont v))
    | Write_var r v cont => Write_var r v (fun u => fmap f (cont u))
    | Get_config l key t cont => Get_config l key t (fun v => fmap f (cont v))
    | Get_undefined l t cont => Get_undefined l t (fun v => fmap f (cont v))
    end.

  Definition pure {A : Type} (x : A) : M A := Pure x.

  Definition lift_option {A : Type} (l : Ast.loc) (x : option A) : M A :=
    match x with
    | Some y => Pure y
    | None => Runtime_type_error l
    end.

  Definition lift_sum {A : Type} (mr : Ast.loc + A) : M A :=
    match mr with
    | inl l => Runtime_type_error l
    | inr r => Pure r
    end.

  Fixpoint sequence {A : Type} (ls : list (M A)) : M (list A) :=
    match ls with
    | m :: ms => bind m (fun x => bind (sequence ms) (fun xs => pure (x :: xs)))
    | [] => pure []
    end.

  Definition get_config (l : Ast.loc) (key : list string) (typ : Ast.typ) : M V :=
    Get_config l key typ pure.

  Definition get_undefined (l : Ast.loc) (typ : Ast.typ) : M V :=
    Get_undefined l typ pure.

  Definition throw {A : Type} (v : V) : M A := Exception v.

  Inductive caught (A : Type) : Type :=
  | Continue : A → caught A
  | Caught : V → caught A.

  Arguments Continue {_}.
  Arguments Caught {_}.

  Definition catch {A : Type} (m : M A) : M (caught A) :=
    match m with
    | Pure x => Pure (Continue x)
    | Early_return v => Early_return v
    | Exit v => Exit v
    | Exception v => Pure (Caught v)
    | Runtime_type_error l => Runtime_type_error l
    | Match_failure l => Match_failure l
    | Assertion_failed msg => Assertion_failed msg
    | Call id args cont => Call id args (fun v => fmap Continue (cont v))
    | Read_var r cont => Read_var r (fun v => fmap Continue (cont v))
    | Write_var r v cont => Write_var r v (fun _ => fmap Continue (cont ()))
    | Get_config l key t cont => Get_config l key t (fun v => fmap Continue (cont v))
    | Get_undefined l t cont => Get_undefined l t (fun v => fmap Continue (cont v))
    end.

  Lemma bind_left_id : ∀ (A B : Type) (f : A → M B) (x : A), bind (pure x) f = f x.
  Proof.
    reflexivity.
  Qed.

  Lemma bind_right_id : ∀ (A : Type) (m : M A), bind m pure = m.
  Proof.
    intros A m.
    induction m; cbn; try reflexivity.
    all: f_equal.
    all: apply functional_extensionality.
    all: auto.
  Qed.

  Lemma bind_assoc : ∀ (A B C : Type) (f : A → M B) (g : B → M C) (x : M A),
      bind (bind x f) g = bind x (fun y => bind (f y) g).
  Proof.
    intros A B C' f g x.
    induction x; cbn; try reflexivity.
    all: f_equal.
    all: apply functional_extensionality.
    all: auto.
  Qed.
End Monad.

Arguments Continue {_ _}.
Arguments Caught {_ _}.

Notation "x ← y ; z" := (bind y (fun x : _ => z))
  (at level 20, y at level 100, z at level 200, only parsing).
