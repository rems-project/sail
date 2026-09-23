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

(** * Bit, bool and bitvector primitives

Concrete implementations of the Sail bit, bool and bitvector primitives, with
bitvectors defined using stdpp bitvectors.

Internally operations are written over [bv n], so widths are checked statically
and the stdpp lemma library applies. Extraction erases that index, however, so
at the boundary bitvectors are [bvn]. *)

From Stdlib Require Import Ascii.
From Stdlib Require Import String.
From Stdlib Require Import ZArith.

From stdpp Require Import bitvector.definitions.

From Sail Require Import Bit.
From Sail Require Import BvUtil.
From Sail Require Import ListUtil.
From Sail Require PrimVector.

Open Scope Z_scope.

(** The width of a bitvector, as a Sail integer. *)
Definition length (x : bvn) : Z := Z.of_N x.(bvn_n).

(** Full adder on bits, returning [(sum, carry_out)]. *)
Definition add_bit_with_carry (x y carry : bit) : bit * bit :=
  match x, y, carry with
  | B0, B0, B0 => (B0, B0)
  | B0, B1, B0 => (B1, B0)
  | B1, B0, B0 => (B1, B0)
  | B1, B1, B0 => (B0, B1)
  | B0, B0, B1 => (B1, B0)
  | B0, B1, B1 => (B0, B1)
  | B1, B0, B1 => (B0, B1)
  | B1, B1, B1 => (B1, B1)
  end.

(** Full subtractor on bits, returning [(difference, borrow_out)]. *)
Definition sub_bit_with_carry (x y carry : bit) : bit * bit :=
  match x, y, carry with
  | B0, B0, B0 => (B0, B0)
  | B0, B1, B0 => (B0, B1)
  | B1, B0, B0 => (B1, B0)
  | B1, B1, B0 => (B0, B0)
  | B0, B0, B1 => (B1, B0)
  | B0, B1, B1 => (B0, B0)
  | B1, B0, B1 => (B1, B1)
  | B1, B1, B1 => (B1, B0)
  end.

(** ** Conversions out of [bit] *)

Definition bool_of_bit (b : bit) : bool := bit_to_bool b.

Definition bit_of_bool (b : bool) : bit := bool_to_bit b.

Definition string_of_bit (b : bit) : string :=
  match b with
  | B0 => "0"%string
  | B1 => "1"%string
  end.

Definition char_of_bit (b : bit) : ascii :=
  match b with
  | B0 => "0"%char
  | B1 => "1"%char
  end.

(** FIXME: [sail_lib.ml] carries two names for this, [big_int_of_bit] and
    [bigint_of_bit]; both alias this single definition. *)
Definition bigint_of_bit (b : bit) : Z :=
  match b with
  | B0 => 0
  | B1 => 1
  end.

(** ** Bool primitives *)

Definition and_bool (x y : bool) : bool := andb x y.

Definition or_bool (x y : bool) : bool := orb x y.

Definition xor_bool (x y : bool) : bool := xorb x y.

Definition eq_bool (x y : bool) : bool := Bool.eqb x y.

(** ** Bitlist conversion *)

Definition of_bit_list (xs : list bit) : bvn := Bits.to_bvn xs.

Definition to_bit_list (x : bvn) : list bit :=
  List.map bool_to_bit (List.rev (bv_to_bits x.(bvn_val))).

Lemma to_of_bit_list : ∀ xs, to_bit_list (of_bit_list xs) = xs.
Proof.
  intro xs.
  unfold to_bit_list, of_bit_list, Bits.to_bvn.
  cbn.
  rewrite BoolList.bv_round_trip_alt.
  rewrite List.rev_involutive.
  rewrite List.map_map.
  induction xs as [| x xs IH]; cbn; [reflexivity |].
  rewrite IH; destruct x; reflexivity.
Qed.

Definition width (x : bvn) : Z := Z.of_N x.(bvn_n).

Lemma width_of_bit_list : ∀ xs, width (of_bit_list xs) = Z.of_nat (List.length xs).
Proof.
  intro xs.
  unfold width, of_bit_list, Bits.to_bvn.
  cbn.
  rewrite List.length_map.
  rewrite nat_N_Z.
  reflexivity.
Qed.

Definition bits_eqb (xs ys : list bit) : bool := list_eqb bit_eqb xs ys.

Definition lift1 (f : ∀ n, bv n → bv n) (x : bvn) : bvn :=
  bv_to_bvn (f x.(bvn_n) x.(bvn_val)).

Definition lift2 (f : ∀ n, bv n → bv n → bv n) (x y : bvn) : option bvn :=
  match bvn_to_bv x.(bvn_n) y with
  | Some y' => Some (bv_to_bvn (f x.(bvn_n) x.(bvn_val) y'))
  | None => None
  end.

(** ** Bitwise operations *)

Definition not_vec (x : bvn) : bvn := lift1 (fun n => bv_not) x.

Definition and_vec (x y : bvn) : option bvn := lift2 (fun n => bv_and) x y.

Definition or_vec (x y : bvn) : option bvn := lift2 (fun n => bv_or) x y.

Definition xor_vec (x y : bvn) : option bvn := lift2 (fun n => bv_xor) x y.

Definition uint (x : bvn) : Z := bv_unsigned x.(bvn_val).

Definition sint (x : bvn) : Z := bv_signed x.(bvn_val).

Definition zeros (n : Z) : bvn := bv_0 (Z.to_N n).

Definition ones (n : Z) : bvn := bv_not (bv_0 (Z.to_N n)).

Definition zrange (lo hi : Z) : list Z :=
  List.map (fun k => lo + Z.of_nat k) (List.seq 0 (S (Z.to_nat (hi - lo)))).

Definition zero_extend (x : bvn) (n : Z) : bvn :=
  bv_zero_extend (Z.to_N n) x.(bvn_val).

Definition sign_extend (x : bvn) (n : Z) : bvn :=
  bv_sign_extend (Z.to_N n) x.(bvn_val).

Definition shiftr (x : bvn) (y : Z) : bvn :=
  Z_to_bv x.(bvn_n) (Z.shiftr (bv_unsigned x.(bvn_val)) y).

Definition shiftl (x : bvn) (y : Z) : bvn :=
  Z_to_bv x.(bvn_n) (Z.shiftl (bv_unsigned x.(bvn_val)) y).

Definition arith_shiftr (x : bvn) (y : Z) : bvn :=
  Z_to_bv x.(bvn_n) (Z.shiftr (bv_signed x.(bvn_val)) y).

Definition shiftr_ref (xs : list bit) (y : Z) : list bit :=
  PrimVector.take (Z.of_nat (List.length xs)) (List.repeat B0 (Z.to_nat y) ++ xs).

Definition shiftl_ref (xs : list bit) (y : Z) : list bit :=
  PrimVector.drop y (xs ++ List.repeat B0 (Z.to_nat y)).

Definition arith_shiftr_ref (xs : list bit) (y : Z) : list bit :=
  PrimVector.take (Z.of_nat (List.length xs))
    (List.concat (List.repeat (PrimVector.take 1 xs) (Z.to_nat y)) ++ xs).

Definition shift_bits_right (x y : bvn) : bvn := shiftr x (uint y).
Definition shift_bits_left (x y : bvn) : bvn := shiftl x (uint y).
Definition shift_bits_right_arith (x y : bvn) : bvn := arith_shiftr x (uint y).

Definition get_slice_int (n m o : Z) : bvn := Z_to_bv (Z.to_N n) (Z.shiftr m o).

Definition to_bits (len n : Z) : bvn := Z_to_bv (Z.to_N len) n.

Fixpoint get_slice_int_ref_aux (k : nat) (m o : Z) : list bit :=
  match k with
  | O => []
  | S k => (if Z.testbit m (Z.of_nat k + o) then B1 else B0) :: get_slice_int_ref_aux k m o
  end.

Definition get_slice_int_ref (n m o : Z) : list bit := get_slice_int_ref_aux (Z.to_nat n) m o.

Definition to_bits_ref (len n : Z) : list bit := get_slice_int_ref len n 0.


Definition add_vec (x y : bvn) : option bvn := lift2 (fun n => bv_add) x y.
Definition sub_vec (x y : bvn) : option bvn := lift2 (fun n => bv_sub) x y.

Definition add_vec_int (x : bvn) (n : Z) : bvn := bv_add_Z x.(bvn_val) n.
Definition sub_vec_int (x : bvn) (n : Z) : bvn := bv_sub_Z x.(bvn_val) n.

Definition count_leading_zeros (x : bvn) : Z :=
  let v := bv_unsigned x.(bvn_val) in
  if Z.eqb v 0 then width x else width x - (Z.log2 v + 1).

Definition count_trailing_zeros (x : bvn) : Z :=
  let v := bv_unsigned x.(bvn_val) in
  if Z.eqb v 0 then width x else Z.log2 (Z.land v (- v)).

Fixpoint count_leading_zeros_ref (xs : list bit) : Z :=
  match xs with
  | B0 :: xs => 1 + count_leading_zeros_ref xs
  | _ => 0
  end.

Definition count_trailing_zeros_ref (xs : list bit) : Z :=
  count_leading_zeros_ref (List.rev xs).

Definition append (x y : bvn) : bvn :=
  bv_concat (x.(bvn_n) + y.(bvn_n)) x.(bvn_val) y.(bvn_val).

Definition eq_bits (x y : bvn) : bool :=
  andb (N.eqb x.(bvn_n) y.(bvn_n))
       (Z.eqb (bv_unsigned x.(bvn_val)) (bv_unsigned y.(bvn_val))).

Lemma eq_bits_refl : ∀ x, eq_bits x x = true.
Proof.
  intro x; unfold eq_bits.
  rewrite N.eqb_refl, Z.eqb_refl; reflexivity.
Qed.

Lemma eq_bits_comm : ∀ x y, eq_bits x y = eq_bits y x.
Proof.
  intros x y; unfold eq_bits.
  rewrite N.eqb_sym, Z.eqb_sym; reflexivity.
Qed.

Lemma eq_bits_trans : ∀ x y z,
  eq_bits x y = true → eq_bits y z = true → eq_bits x z = true.
Proof.
  intros x y z Hxy Hyz; unfold eq_bits in *.
  apply andb_prop in Hxy as [Hn1 Hv1].
  apply andb_prop in Hyz as [Hn2 Hv2].
  apply N.eqb_eq in Hn1, Hn2.
  apply Z.eqb_eq in Hv1, Hv2.
  apply andb_true_intro; split.
  - apply N.eqb_eq. rewrite Hn1. exact Hn2.
  - apply Z.eqb_eq. rewrite Hv1. exact Hv2.
Qed.

Definition mult_vec (x y : bvn) : bvn := to_bits (2 * width x) (uint x * uint y).
Definition mults_vec (x y : bvn) : bvn := to_bits (2 * width x) (sint x * sint y).

Definition subrange (x : bvn) (n m : Z) : bvn :=
  bv_extract (Z.to_N m) (Z.to_N (n - m + 1)) x.(bvn_val).

Definition slice (x : bvn) (n m : Z) : bvn :=
  bv_extract (Z.to_N n) (Z.to_N m) x.(bvn_val).

Definition access (x : bvn) (n : Z) : bvn := bv_extract (Z.to_N n) 1 x.(bvn_val).

Definition update_bit (x : bvn) (n : Z) (b : bit) : bvn :=
  let v := bv_unsigned x.(bvn_val) in
  Z_to_bv x.(bvn_n)
    (if bit_to_bool b then Z.lor v (Z.shiftl 1 n) else Z.land v (Z.lnot (Z.shiftl 1 n))).

Definition update_subrange (x : bvn) (n m : Z) (y : bvn) : bvn :=
  let w := n - m + 1 in
  let mask := Z.shiftl (Z.pred (Z.shiftl 1 w)) m in
  Z_to_bv x.(bvn_n)
    (Z.lor (Z.land (bv_unsigned x.(bvn_val)) (Z.lnot mask))
           (Z.shiftl (Z.land (uint y) (Z.pred (Z.shiftl 1 w))) m)).

Definition set_slice (out : bvn) (n : Z) (slice : bvn) : bvn :=
  update_subrange out (n + width slice - 1) n slice.

Definition set_slice_int (slice_len m n : Z) (slice : bvn) : Z :=
  let mask := Z.shiftl (Z.pred (Z.shiftl 1 slice_len)) n in
  Z.lor (Z.land m (Z.lnot mask)) (Z.shiftl (uint slice) n).

Definition set_slice_int_ref (slice_len m n : Z) (slice : bvn) : Z :=
  let mask := Z.shiftl (Z.pred (Z.shiftl 1 slice_len)) n in
  Z.lor (Z.lxor (Z.lor mask m) mask) (Z.shiftl (uint slice) n).

Definition subrange_inc (x : bvn) (n m : Z) : bvn :=
  subrange x (width x - 1 - n) (width x - 1 - m).

Definition slice_inc (x : bvn) (n m : Z) : bvn :=
  subrange x (width x - 1 - n) (width x - m - n).

Definition access_inc (x : bvn) (n : Z) : bvn := access x (width x - 1 - n).

Definition update_bit_inc (x : bvn) (n : Z) (b : bit) : bvn :=
  update_bit x (width x - 1 - n) b.

Definition add_vec_carry (x y : bvn) : option (bit * bvn) :=
  match add_vec x y with
  | None => None
  | Some sum =>
      let carry := Z.leb (Z.pow 2 (width x)) (uint x + uint y) in
      Some (bool_to_bit carry, sum)
  end.

Fixpoint replicate_bits_aux (k : nat) (x acc : bvn) : bvn :=
  match k with
  | O => acc
  | S k => replicate_bits_aux k x (append acc x)
  end.

Definition replicate_bits (x : bvn) (n : Z) : bvn :=
  replicate_bits_aux (Z.to_nat n) x (zeros 0).

Definition vector_truncate (x : bvn) (n : Z) : bvn := bv_zero_extend (Z.to_N n) x.(bvn_val).

Definition vector_truncateLSB (x : bvn) (n : Z) : bvn :=
  subrange x (width x - 1) (width x - n).

Fixpoint reverse_endianness_fuel (fuel : nat) (x : bvn) : bvn :=
  match fuel with
  | O => x
  | S fuel =>
      if Z.leb (width x) 8 then
        x
      else
        append (reverse_endianness_fuel fuel (subrange x (width x - 9) 0))
               (subrange x (width x - 1) (width x - 8))
  end.

Definition reverse_endianness (x : bvn) : bvn :=
  reverse_endianness_fuel (N.to_nat x.(bvn_n)) x.

Definition split_at (s : Z) (x : bvn) : bvn * bvn :=
  let w := width x in
  let k := Z.max 0 (Z.min s w) in
  (subrange x (w - 1) (w - k), subrange x (w - k - 1) 0).

Definition to_single_bits (x : bvn) : list bvn :=
  List.map (fun b => of_bit_list [b]) (to_bit_list x).
