/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_ARITH_INTERNAL
$define _FLOAT_ARITH_INTERNAL

$include <float/common.sail>
$include <float/zero.sail>
$include <float/nan.sail>
$include <float/rounding.sail>

val      float_is_lt_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_lt_internal (op_0, op_1) = {
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  let is_zero      = float_is_zero (op_0) & float_is_zero (op_1);
  let diff_sign_lt = is_lowest_one (fp_0.sign) & not_bool (is_zero);

  let is_neg       = is_lowest_one (fp_0.sign);
  let unsigned_lt  = unsigned (op_0) < unsigned (op_1);
  let is_xor       = (is_neg & not_bool (unsigned_lt)) | (not_bool (is_neg) & unsigned_lt);
  let same_sign_lt = (op_0 != op_1) & is_xor;

  let is_lt = if   fp_0.sign != fp_1.sign
              then diff_sign_lt
              else same_sign_lt;

  is_lt;
}

val      float_is_eq_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_eq_internal (op_0, op_1) = {
  let is_zero = float_is_zero (op_0) & float_is_zero (op_1);
  let is_eq   = (op_0 == op_1) | is_zero;

  is_eq;
}

val      float_is_ne_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_ne_internal (op_0, op_1)
  = not_bool (float_is_eq_internal (op_0, op_1))

val      float_is_le_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_le_internal (op_0, op_1)
  = float_is_eq_internal (op_0, op_1) | float_is_lt_internal (op_0, op_1)

val      float_is_gt_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_gt_internal (op_0, op_1)
  = not_bool (float_is_le_internal (op_0, op_1))

val      float_is_ge_internal : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> bool
function float_is_ge_internal (op_0, op_1)
  = not_bool (float_is_lt_internal (op_0, op_1))

val      float_propagate_nan : forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_propagate_nan (op_0, op_1) = {
  let is_snan = float_is_snan (op_0) | float_is_snan (op_1);
  let flags = if is_snan then fp_eflag_invalid else fp_eflag_none;

  let one = sail_zero_extend ([bitone], length (op_0));
  let fp_0 = float_decompose (op_0);
  let mask = sail_shiftleft (one, length (fp_0.mantissa) - 1);
  let op = if float_is_nan (op_0) then op_0 else op_1;

  ((op | mask), flags)
}

val      float_rounding_increment : forall 'n, 'n in {16, 32, 64, 128}.
  (bits(1), bits('n), fp_rounding_modes) -> bits('n)
function float_rounding_increment (sign, op, rounding_mode) = {
  let bitsize = length (op);
  let fp = float_decompose (op);
  let is_rne = rounding_mode == fp_rounding_rne;
  let is_rna = rounding_mode == fp_rounding_rna;
  let not_rne_and_rna = not_bool (is_rne) & not_bool (is_rna);
  let rounding_inf = if sign == [bitone] then fp_rounding_rdn else fp_rounding_rup;

  let one = sail_zero_extend ([bitone], bitsize);

  if not_rne_and_rna & rounding_mode == rounding_inf then
    sub_bits (sail_shiftleft (one, length (fp.exp) - 1), one)
  else if not_rne_and_rna & rounding_mode != rounding_inf then
    sail_zeros ('n)
  else
    sail_shiftleft (one, length (fp.exp) - 2)
}

val      float_compose_after_round : forall 'n, 'n in {16, 32, 64, 128}.
  (bits(1), bits('n), bits('n), bits('n), fp_rounding_modes) -> (bits('n), fp_exception_flags)
function float_compose_after_round (sign, exp, mantissa, increment, rounding_mode) = {
  let bitsize = length (mantissa);
  let fp = float_decompose (mantissa);
  let one = sail_zero_extend ([bitone], bitsize);
  let zero = sail_zero_extend ([bitzero], bitsize);

  let round_mask = sub_bits (sail_shiftleft (one, length (fp.exp) - 1), one);
  let round_bits = mantissa & round_mask;
  let eflag = if is_all_zeros (round_bits) then fp_eflag_none else fp_eflag_inexact;

  let rne_mask = if rounding_mode == fp_rounding_rne then one else zero;
  let cst_mask = sail_shiftleft (one, length (fp.exp) - 2);
  let xor_mask = xor_vec (round_bits, cst_mask);
  let not_mask = if is_all_zeros (xor_mask) then one else zero;
  let and_mask = and_vec (not_mask, rne_mask);
  let mantissa_mask = not_vec (and_mask);

  let offset = length (fp.exp) - 1;
  let mantissa_round = sail_shiftright (mantissa + increment, offset);
  let mantissa_new = and_vec (mantissa_round, mantissa_mask);
  let exp_new = if is_all_zeros (mantissa_new) then sail_zeros ('n) else exp;
  let exp_shift = sail_shiftleft (exp_new, length (fp.mantissa));

  let exp_and_mantissa = truncate (exp_shift + mantissa_new, bitsize - 1);

  (sign @ exp_and_mantissa, eflag);
}

val      float_get_sign_with_all_ones_exp : forall 'n, 'n in {16, 32, 64, 128}.
  (bits(1), bits('n)) -> bits('n)
function float_get_sign_with_all_ones_exp (sign, op) = {
  let bitsize = length (op);
  let fp = float_decompose (op);
  let one = sail_zero_extend ([bitone], bitsize);
  let all_ones = sub_bits (sail_shiftleft (one, length (fp.exp)), one);
  let all_ones_exp = sail_shiftleft (all_ones, length (fp.mantissa));

  sign @ truncate (all_ones_exp, bitsize - 1);
}

val      float_round_and_compose : forall 'n, 'n in {16, 32, 64, 128}.
  (bits(1), bits('n), bits('n), fp_rounding_modes) -> (bits('n), fp_exception_flags)
function float_round_and_compose (sign, exp, mantissa, rounding_mode) = {
  let op = mantissa;
  let fp = float_decompose (op);
  let bitsize = length (op);
  let one = sail_zero_extend ([bitone], bitsize);
  let zero = sail_zero_extend ([bitzero], bitsize);
  let three = sail_zero_extend ([bitone, bitone], bitsize);
  let increment = float_rounding_increment (sign, mantissa, rounding_mode);

  let exp_limit = sub_bits (sail_shiftleft (one, length (fp.exp)), three);
  let exp_reach_limit = not_bool (unsigned (exp) < unsigned (exp_limit));
  let exp_overflow = unsigned (exp) > unsigned (exp_limit);

  let mantissa_limit = sail_shiftleft (one, bitsize - 1);
  let mantissa_overflow = not_bool (unsigned (mantissa_limit)
    > unsigned (mantissa) + unsigned(increment));

  if exp_reach_limit & (exp_overflow | mantissa_overflow) then {
    let result = float_get_sign_with_all_ones_exp (sign, op);
    let tail = if is_all_zeros (increment) then one else zero;

    (sub_bits (result, tail), fp_eflag_overflow_and_inexact)
  } else {
    float_compose_after_round (sign, exp, mantissa, increment, rounding_mode);
  }
}

val      float_add_same_exp_internal : forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_add_same_exp_internal (op_0, op_1) = {
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  let bitsize = length (op_0);
  let mantissa_0 = sail_zero_extend (fp_0.mantissa, bitsize);
  let mantissa_1 = sail_zero_extend (fp_1.mantissa, bitsize);
  let mantissa_sum = mantissa_0 + mantissa_1;

  let sign = fp_0.sign;
  let no_round = is_lowest_zero (mantissa_sum) & not_bool (float_has_max_exp (op_0));

  if no_round then {
    let mantissa_shift = sail_shiftright (mantissa_sum, 1);
    let mantissa_bitsize = length (fp_0.mantissa);

    let exp = fp_0.exp + sail_zero_extend ([bitone], length (fp_0.exp));
    let mantissa = truncate (mantissa_shift, mantissa_bitsize);

    (sign @ exp @ mantissa, fp_eflag_none);
  } else {
    let exp = sail_zero_extend (fp_0.exp, bitsize);
    let shift_bitsize = length (fp_0.mantissa) + 1;
    let one = sail_zero_extend ([bitone], bitsize);
    let mantissa_offset = mantissa_sum + sail_shiftleft (one, shift_bitsize);
    let mantissa = sail_shiftleft (mantissa_offset, length (fp_0.exp) - 2);
    let rm = float_get_rounding ();

    float_round_and_compose (sign, exp, mantissa, rm);
  }
}

val      float_add_same_exp: forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_add_same_exp (op_0, op_1) = {
  let bitsize = length (op_0);
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  assert (fp_0.exp == fp_1.exp, "The exp of floating point must be same.");

  let is_exp_0_all_ones = is_all_ones (fp_0.exp);
  let is_mantissa_all_zeros = is_all_zeros (fp_0.mantissa | fp_1.mantissa);

  if is_all_zeros (fp_0.exp) then
    (op_0 + sail_zero_extend (fp_1.mantissa, bitsize), fp_eflag_none)
  else if is_exp_0_all_ones & is_mantissa_all_zeros then
    (op_0, fp_eflag_none)
  else if is_exp_0_all_ones & not_bool (is_mantissa_all_zeros) then
    float_propagate_nan (op_0, op_1)
  else
    float_add_same_exp_internal (op_0, op_1);
}

val      float_add_less_than_exp: forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_add_less_than_exp (op_0, op_1) = {
  let bitsize = length (op_0);
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  assert (unsigned (fp_0.exp) < unsigned (fp_1.exp),
    "The exp of floating point op_0 must be less than op_1.");

  let is_exp_all_ones = is_all_ones (fp_1.exp);
  let mantissa_shift = sail_shiftleft (fp_1.mantissa, length (fp_1.exp) - 2);
  let is_nan = not_bool (is_all_zeros (mantissa_shift));

  if is_exp_all_ones & is_nan then
    float_propagate_nan (op_0, op_1)
  else if is_exp_all_ones then {
    (float_get_sign_with_all_ones_exp (fp_0.sign, op_0), fp_eflag_none)
  } else {
    assert (false, "Not implemented yet.");
    (sail_zeros ('n), fp_eflag_none);
  }
}

val      float_add_diff_exp: forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_add_diff_exp (op_0, op_1) = {
  let bitsize = length (op_0);
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  assert (fp_0.exp != fp_1.exp, "The exp of floating point cannot be same.");

  if unsigned (fp_0.exp) < unsigned (fp_1.exp) then
    float_add_less_than_exp (op_0, op_1)
  else {
    assert (false, "Not implemented yet.");
    (sail_zeros ('n), fp_eflag_none);
  }
}

val      float_add_internal : forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_add_internal (op_0, op_1) = {
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  assert (xor_vec (fp_0.sign, fp_1.sign) == [bitzero],
    "The sign of float add operand 0 and operand 1 must be the same.");

  if fp_0.exp == fp_1.exp then
    float_add_same_exp (op_0, op_1)
  else
    float_add_diff_exp (op_0, op_1)
}

val      float_sub_internal : forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_sub_internal (_op_0, _op_1) = {
  assert (false, "Not implemented yet.");
  (sail_zeros ('n), fp_eflag_none);
}

$endif
