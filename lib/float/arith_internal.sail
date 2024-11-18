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

val      float_is_lt_internal : fp_bits_x2 -> bool
function float_is_lt_internal ((op_0, op_1)) = {
  let fp_0 = float_decompose (op_0);
  let fp_1 = float_decompose (op_1);

  let is_zero      = float_is_zero (op_0) & float_is_zero (op_1);
  let diff_sign_lt = is_lowest_one (fp_0.sign) & not (is_zero);

  let is_neg       = is_lowest_one (fp_0.sign);
  let unsigned_lt  = unsigned (op_0) < unsigned (op_1);
  let is_xor       = (is_neg & not (unsigned_lt)) | (not (is_neg) & unsigned_lt);
  let same_sign_lt = (op_0 != op_1) & is_xor;

  let is_lt = if   fp_0.sign != fp_1.sign
              then diff_sign_lt
              else same_sign_lt;

  is_lt;
}

val      float_is_eq_internal : fp_bits_x2 -> bool
function float_is_eq_internal ((op_0, op_1)) = {
  let is_zero = float_is_zero (op_0) & float_is_zero (op_1);
  let is_eq   = (op_0 == op_1) | is_zero;

  is_eq;
}

val      float_is_ne_internal : fp_bits_x2 -> bool
function float_is_ne_internal ((op_0, op_1))
  = not (float_is_eq_internal ((op_0, op_1)))

val      float_is_le_internal : fp_bits_x2 -> bool
function float_is_le_internal ((op_0, op_1))
  = float_is_eq_internal ((op_0, op_1)) | float_is_lt_internal ((op_0, op_1))

val      float_is_gt_internal : fp_bits_x2 -> bool
function float_is_gt_internal ((op_0, op_1))
  = not (float_is_le_internal ((op_0, op_1)))

val      float_is_ge_internal : fp_bits_x2 -> bool
function float_is_ge_internal ((op_0, op_1))
  = not (float_is_lt_internal ((op_0, op_1)))

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
  else if is_exp_0_all_ones & not (is_mantissa_all_zeros) then
    float_propagate_nan (op_0, op_1)
  else {
    assert (false, "Not implemented yet.");
    (sail_zeros ('n), fp_eflag_none);
  };
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
  else {
    assert (false, "Not implemented yet.");
    (sail_zeros ('n), fp_eflag_none);
  }
}

val      float_sub_internal : forall 'n, 'n in {16, 32, 64, 128}.
  (bits('n), bits('n)) -> (bits('n), fp_exception_flags)
function float_sub_internal (op_0, op_1) = {
  assert (false, "Not implemented yet.");
  (sail_zeros ('n), fp_eflag_none);
}

$endif
