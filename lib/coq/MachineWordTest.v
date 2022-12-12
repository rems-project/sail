From Sail Require Import MachineWord.
From stdpp Require Import bitvector.
Require Import ZArith.

Import MachineWord.
Open Scope Z.

Transparent Z_to_bv
       bv_0 bv_succ bv_pred
       bv_add bv_sub bv_opp
       bv_mul bv_divu bv_modu
       bv_divs bv_quots bv_mods bv_rems
       bv_shiftl bv_shiftr bv_ashiftr bv_or
       bv_and bv_xor bv_not bv_zero_extend
       bv_sign_extend bv_extract bv_concat
       bv_add_Z bv_sub_Z bv_mul_Z
       bool_to_bv bv_to_bits.


Example zeros_3 : word_to_Z (zeros 3) = 0.
reflexivity.
Qed.

Example ones_3 : word_to_Z (ones 3) = -1.
compute.
reflexivity.
Qed.

Example ones_3_N : word_to_N (ones 3) = 7%N.
reflexivity.
Qed.

Example get_bit_5 :
  get_bit (N_to_word 4 5) 0 = true /\
  get_bit (N_to_word 4 5) 1 = false /\
  get_bit (N_to_word 4 5) 2 = true.
compute.
auto.
Qed.

Example set_bit_5 :
  set_bit (N_to_word 4 5) 0 false = N_to_word 4 4 /\
  set_bit (N_to_word 4 5) 1 true  = N_to_word 4 7 /\
  set_bit (N_to_word 4 5) 2 false = N_to_word 4 1 /\
  set_bit (N_to_word 4 5) 0 true  = N_to_word 4 5 /\
  set_bit (N_to_word 4 5) 1 false = N_to_word 4 5 /\
  set_bit (N_to_word 4 5) 2 true  = N_to_word 4 5.
compute.
auto 7.
Qed.

Example word_to_bools_5 : word_to_bools (N_to_word 4 5) = [false; true; false; true].
compute.
reflexivity.
Qed.

Example bools_to_word_5 : N_to_word 4 5 = bools_to_word [false; true; false; true].
reflexivity.
Qed.

Example Z_word_Z :
  word_to_Z (Z_to_word 4 3) = 3 /\
  word_to_Z (Z_to_word 4 5) = 5 /\
  word_to_Z (Z_to_word 5 5) = 5 /\
  word_to_Z (Z_to_word 10 17) = 17 /\
  word_to_Z (Z_to_word 4 (-3)) = -3 /\
  word_to_Z (Z_to_word 4 (-5)) = -5 /\
  word_to_Z (Z_to_word 5 (-5)) = -5 /\
  word_to_Z (Z_to_word 10 (-17)) = -17.
compute.
auto 10.
Qed.

Local Open Scope N.
Example N_word_N :
  word_to_N (N_to_word 4 3) = 3 /\
  word_to_N (N_to_word 4 5) = 5 /\
  word_to_N (N_to_word 5 5) = 5 /\
  word_to_N (N_to_word 10 17) = 17 /\
  word_to_N (N_to_word 4 11) = 11 /\
  word_to_N (N_to_word 4 13) = 13 /\
  word_to_N (N_to_word 5 21) = 21.
compute.
auto 10.
Qed.
Close Scope N.

Example slice_5 : slice 2 (Z_to_word 10 5) 1 = Z_to_word 2 2.
reflexivity.
Qed.

Example update_slice_5 : update_slice (Z_to_word 10 5) 1 (Z_to_word 2 3) = Z_to_word 10 7.
compute.
reflexivity.
Qed.

Example zero_extend_5 :
  zero_extend 10 (Z_to_word 4 5) = Z_to_word 10 5 /\
  zero_extend 10 (Z_to_word 3 5) = Z_to_word 10 5.
compute.
auto.
Qed.

Example sign_extend_5 :
  sign_extend 10 (Z_to_word 4 5) = Z_to_word 10 5 /\
  sign_extend 10 (Z_to_word 3 5) = Z_to_word 10 (-3).
compute.
auto.
Qed.

Example concat_5 : concat (Z_to_word 4 5) (Z_to_word 5 5) = bools_to_word [false; true; false; true; false; false; true; false; true].
compute.
reflexivity.
Qed.

Example and_5 :
  eqb (and (Z_to_word 4 5) (Z_to_word 4 5)) (Z_to_word 4 5) = true /\
  eqb (and (Z_to_word 4 7) (Z_to_word 4 5)) (Z_to_word 4 5) = true /\
  eqb (and (Z_to_word 4 5) (Z_to_word 4 1)) (Z_to_word 4 1) = true.
compute.
auto.
Qed.

Example or_5 :
  eqb (or (Z_to_word 4 5) (Z_to_word 4 5)) (Z_to_word 4 5) = true /\
  eqb (or (Z_to_word 4 7) (Z_to_word 4 5)) (Z_to_word 4 7) = true /\
  eqb (or (Z_to_word 4 5) (Z_to_word 4 1)) (Z_to_word 4 5) = true.
compute.
auto.
Qed.

Example xor_5 :
  eqb (xor (Z_to_word 4 5) (Z_to_word 4 5)) (Z_to_word 4 0) = true /\
  eqb (xor (Z_to_word 4 7) (Z_to_word 4 5)) (Z_to_word 4 2) = true /\
  eqb (xor (Z_to_word 4 5) (Z_to_word 4 1)) (Z_to_word 4 4) = true.
compute.
auto.
Qed.

Example not_5 : eqb (not (Z_to_word 4 5)) (Z_to_word 4 (-6)) = true.
compute.
reflexivity.
Qed.

Example add_5 :
  eqb (add (Z_to_word 4 5) (Z_to_word 4 0)) (Z_to_word 4 5) = true /\
  eqb (add (Z_to_word 4 5) (Z_to_word 4 2)) (Z_to_word 4 7) = true /\
  eqb (add (Z_to_word 4 5) (Z_to_word 4 3)) (Z_to_word 4 (-8)) = true.
compute.
auto.
Qed.

Example sub_5 :
  eqb (sub (Z_to_word 4 5) (Z_to_word 4 0)) (Z_to_word 4 5) = true /\
  eqb (sub (Z_to_word 4 5) (Z_to_word 4 2)) (Z_to_word 4 3) = true /\
  eqb (sub (Z_to_word 4 5) (Z_to_word 4 3)) (Z_to_word 4 2) = true.
compute.
auto.
Qed.

Example mul_5 :
  eqb (mul (Z_to_word 4 5) (Z_to_word 4 0)) (Z_to_word 4 0) = true /\
  eqb (mul (Z_to_word 4 5) (Z_to_word 4 2)) (Z_to_word 4 10) = true /\
  eqb (mul (Z_to_word 4 5) (Z_to_word 4 3)) (Z_to_word 4 15) = true.
compute.
auto.
Qed.

Example lsl :
  eqb (logical_shift_left (Z_to_word 4 5) 0) (Z_to_word 4 5) = true /\
  eqb (logical_shift_left (Z_to_word 4 5) 1) (Z_to_word 4 10) = true /\
  eqb (logical_shift_left (Z_to_word 4 5) 3) (Z_to_word 4 8) = true.
compute.
auto.
Qed.

Example lsr :
  eqb (logical_shift_right (Z_to_word 4 5) 0) (Z_to_word 4 5) = true /\
  eqb (logical_shift_right (Z_to_word 4 5) 1) (Z_to_word 4 2) = true /\
  eqb (logical_shift_right (Z_to_word 4 5) 3) (Z_to_word 4 0) = true.
compute.
auto.
Qed.

Example asr :
  eqb (arith_shift_right (Z_to_word 4 5) 0) (Z_to_word 4 5) = true /\
  eqb (arith_shift_right (Z_to_word 4 5) 1) (Z_to_word 4 2) = true /\
  eqb (arith_shift_right (Z_to_word 4 5) 3) (Z_to_word 4 0) = true /\
  eqb (arith_shift_right (Z_to_word 3 5) 0) (Z_to_word 3 5) = true /\
  eqb (arith_shift_right (Z_to_word 3 5) 1) (Z_to_word 3 6) = true /\
  eqb (arith_shift_right (Z_to_word 3 5) 3) (Z_to_word 3 7) = true.
compute.
auto 10.
Qed.

Example replicate_5 :
  eqb (replicate 1 (Z_to_word 4 5)) (Z_to_word 4 5) = true /\
  eqb (replicate 2 (Z_to_word 4 5)) (Z_to_word 8 85) = true /\
  eqb (replicate 3 (Z_to_word 4 5)) (Z_to_word 12 1365) = true.
compute.
auto 10.
Qed.

Example reverse_endian_5 :
  eqb (reverse_endian (Z_to_word 8 5)) (Z_to_word 8 5) = true /\
  eqb (reverse_endian (Z_to_word 16 5)) (Z_to_word 16 1280) = true.
compute.
auto.
Qed.
