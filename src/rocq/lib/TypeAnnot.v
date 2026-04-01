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

(** * Information from type annotations

Sail annotates terms with custom type annotation data, which we
don't have access to here. Instead whenever we need to access
information from these annotations, we use a functor parameterised by
the signature [S], which provides the methods we need.

This file is not intended to be imported unqualified. Other modules
can import the [Types] submodule to use those inductives unqualified
however. *)

From Stdlib Require Import Unicode.Utf8.

From Sail Require Import Ast.

Module Types.
  (** Type annotations are used to disambiguate identifiers in the Sail AST. *)
  Inductive id_type : Set :=
  | Local_variable : id_type
  | Global_register : id_type
  | Enum_member : id_type.

  (** Type annotations determine how vector concatentation patterns
  << x @ y >> in Sail are split apart. *)
  Inductive vector_concat_split : Set :=
  | No_split : vector_concat_split
  | Split : nat → vector_concat_split.
End Types.

(** The signature contains the following functions:

- [get_type]. Currently only used for [E_undefined]. It would be nice
  to remove this.

- [get_id_type]. See [id_type].

- [get_split]. See [vector_concat_split].

- [is_bitvector]. The bitvector syntax in Sail is overloaded between
  bitvectors and generic vectors, so we use the typing information to
  distinguish the two.

- [fallthrough]. When evaluating try expressions, we need a
  type-annotated expression which is essentially just
  << exn => throw exn >> but we don't have the type-system in Rocq,
  so we get such an expression from this module. This is a little ugly,
  so it would be good to re-define the semantics in a way that avoids
  needing this.
*)

Module Type S.
  Import Types.

  Parameter t : Set.

  Parameter get_type : t → typ.

  Parameter get_id_type : t → id → id_type.

  Parameter get_split : t → vector_concat_split.

  Parameter is_bitvector : t → bool.

  Parameter fallthrough : Ast.pexp t.
End S.
