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

Require Import Ast.
Require Import IdUtil.
Require Import ValueType.
Require PatternMatch.
Require TypeAnnot.

Import ListNotations.

Module Type S (Tannot : TypeAnnot.S).
  Parameter t : Set.

  Parameter join : t -> t -> t.

  Infix "⊔" := join (left associativity, at level 50).

  Parameter v_unit : t.
  Parameter v_list : list t -> t.
  Parameter v_tuple : list t -> t.
  Parameter v_vector : list t -> t.
  Parameter v_ref : id -> t.

  Parameter of_lit : lit -> t.

  Parameter is_unit : t -> bool.
  Parameter is_true : t -> bool.
  Parameter is_false : t -> bool.

  Parameter lookup_field : t -> Ast.id -> t.

  Parameter pattern_match : pat Tannot.t -> t -> PatternMatch.match_result t.
  Parameter complete : PatternMatch.binding t -> t.

  Parameter v_unit_is_unit : is_unit v_unit = true.

(*
  Parameter assoc : forall x y z, (x ⊔ y) ⊔ z = x ⊔ (y ⊔ z).

  Parameter comm : forall x y, x ⊔ y = y ⊔ x.

  Parameter idem : forall x, x ⊔ x = x.
*)
End S.

Module Value (Tannot : TypeAnnot.S) <: S Tannot.
  Definition t : Set := Ast.value.

  Definition join (x y : t) : t := if value_eqb x y then x else V_unknown.

  Infix "⊔" := join (left associativity, at level 50).

  Definition v_unit := V_unit.
  Definition v_list := V_list.
  Definition v_tuple := V_tuple.
  Definition v_vector := V_vector.
  Definition v_ref := V_ref.

  Definition of_lit := value_of_lit.

  Definition is_unit (v : t) : bool := match v with V_unit => true | _ => false end.
  Definition is_true (v : t) : bool := match v with V_bool true => true | _ => false end.
  Definition is_false (v : t) : bool := match v with V_bool false => true | _ => false end.

  Fixpoint lookup_field' (fields : list (id * t)) (name : id) {struct fields} : t :=
    match fields with
    | [] => V_unknown
    | (name', v) :: fields =>
        if id_eqb name name' then
          v
        else
          lookup_field' fields name
    end.

  Definition lookup_field (rec : t) (name : id) : t :=
    match rec with
    | V_record fields => lookup_field' fields name
    | _ => V_unknown
    end.

  Module PM := PatternMatch.Make Tannot.

  Definition pattern_match (p : pat Tannot.t) (v : t) : PatternMatch.match_result t :=
    PM.pattern_match p v.

  Definition complete (b : PatternMatch.binding t) : t :=
    match b with
    | PatternMatch.Complete v => v
    | PatternMatch.Partial vs => PatternMatch.complete_value vs
    end.

  Lemma v_unit_is_unit : is_unit v_unit = true.
  Proof. reflexivity. Qed.
End Value.
