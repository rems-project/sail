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

From Stdlib Require Import Lists.List.

Require Import Ast.
Require Import Bit.

Import ListNotations.

Definition same_bits (bs : list bit) (vs : list bit) : bool :=
  fst (fold_left
         (fun match_info b =>
            match match_info with
            | (_, []) => (false, [])
            | (false, _) => (false, [])
            | (true, B0 :: vs) =>
              match b with
              | B0 => (true, vs)
              | B1 => (false, [])
              end
            | (true, B1 :: vs) =>
              match b with
              | B1 => (true, vs)
              | B0 => (false, [])
              end
            end
         )
         bs
         (true, vs)).

Lemma same_bits_cons : forall (b : bit) (bs : list bit),
    same_bits (b :: bs) (b :: bs) = same_bits bs bs.
Proof.
  intros b bs.
  destruct b.
  all: unfold same_bits.
  all: cbn.
  all: reflexivity.
Qed.

Lemma same_bits_refl : forall (bs : list bit),
    same_bits bs bs = true.
Proof.
  intros bs.
  induction bs.
  easy.
  rewrite same_bits_cons.
  assumption.
Qed.

Definition of_hex_digit (h : hex_digit) : list bit :=
  match h with
  | Hex_0 => [B0; B0; B0; B0]
  | Hex_1 => [B0; B0; B0; B1]
  | Hex_2 => [B0; B0; B1; B0]
  | Hex_3 => [B0; B0; B1; B1]
  | Hex_4 => [B0; B1; B0; B0]
  | Hex_5 => [B0; B1; B0; B1]
  | Hex_6 => [B0; B1; B1; B0]
  | Hex_7 => [B0; B1; B1; B1]
  | Hex_8 => [B1; B0; B0; B0]
  | Hex_9 => [B1; B0; B0; B1]
  | Hex_A => [B1; B0; B1; B0]
  | Hex_B => [B1; B0; B1; B1]
  | Hex_C => [B1; B1; B0; B0]
  | Hex_D => [B1; B1; B0; B1]
  | Hex_E => [B1; B1; B1; B0]
  | Hex_F => [B1; B1; B1; B1]
  end.

Definition hex_digit_of_nibble (b1 b2 b3 b4 : bit) : hex_digit :=
  match (b1, b2, b3, b4) with
  | (B0, B0, B0, B0) => Hex_0
  | (B0, B0, B0, B1) => Hex_1
  | (B0, B0, B1, B0) => Hex_2
  | (B0, B0, B1, B1) => Hex_3
  | (B0, B1, B0, B0) => Hex_4
  | (B0, B1, B0, B1) => Hex_5
  | (B0, B1, B1, B0) => Hex_6
  | (B0, B1, B1, B1) => Hex_7
  | (B1, B0, B0, B0) => Hex_8
  | (B1, B0, B0, B1) => Hex_9
  | (B1, B0, B1, B0) => Hex_A
  | (B1, B0, B1, B1) => Hex_B
  | (B1, B1, B0, B0) => Hex_C
  | (B1, B1, B0, B1) => Hex_D
  | (B1, B1, B1, B0) => Hex_E
  | (B1, B1, B1, B1) => Hex_F
  end.

Fixpoint to_hex_digits (bits : list bit) : option (list hex_digit) :=
  match bits with
  | b1 :: b2 :: b3 :: b4 :: rest =>
      let digit := hex_digit_of_nibble b1 b2 b3 b4 in
      match to_hex_digits rest with
      | None => None
      | Some digits => Some (digit :: digits)
      end
  | [] => Some []
  | _ => None
  end.

Definition non_empty_to_list {A : Set} (xs : non_empty A) : list A :=
  let 'Non_empty y ys := xs in y :: ys.

Definition of_hex_lit (hex : list (non_empty hex_digit)) : list bit :=
  let digits := List.concat (List.map non_empty_to_list hex) in
  List.concat (List.map of_hex_digit digits).

Lemma hex_lit_bitlist_rt : forall (d : hex_digit), to_hex_digits (of_hex_lit [Non_empty d []]) = Some [d].
Proof.
  intros d.
  induction d; cbn; reflexivity.
Qed.

Definition of_bin_lit (bin : list (non_empty bin_digit)) : list bit :=
  let digits := List.concat (List.map non_empty_to_list bin) in
  List.map (fun b =>
      match b with
      | Bin_0 => B0
      | Bin_1 => B1
      end
    ) digits.

Definition to_gvector (v : value) : value :=
  match v with
  | V_bitvector bs => V_vector (List.map (fun b => V_bitvector [b]) bs)
  | v => v
  end.
