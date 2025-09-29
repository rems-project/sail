/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

default Order dec

$include <prelude.sail>
$include <float/add.sail>
$include <float/rounding.sail>
$include "data.sail"
$include "tuple_equality.sail"

function test_float_add () -> unit = {
  /* Half floating point */
  assert(float_add (fp16_pos_subnormal_add_0_op_0, fp16_pos_subnormal_add_0_op_1) == (fp16_pos_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp16_pos_subnormal_add_1_op_0, fp16_pos_subnormal_add_1_op_1) == (fp16_pos_subnormal_add_1_sum, fp_eflag_none));
  assert(float_add (fp16_neg_subnormal_add_0_op_0, fp16_neg_subnormal_add_0_op_1) == (fp16_neg_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp16_neg_subnormal_add_1_op_0, fp16_neg_subnormal_add_1_op_1) == (fp16_neg_subnormal_add_1_sum, fp_eflag_none));

  assert(float_add (fp16_pos_inf, fp16_pos_inf) == (fp16_pos_inf, fp_eflag_none));
  assert(float_add (fp16_pos_inf, fp16_pos_qnan_default) == (fp16_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp16_pos_inf, fp16_pos_qnan_0) == (fp16_pos_qnan_0 | fp16_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp16_pos_inf, fp16_pos_snan_0) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_neg_inf, fp16_neg_inf) == (fp16_neg_inf, fp_eflag_none));
  assert(float_add (fp16_neg_inf, fp16_neg_qnan_default) == (fp16_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp16_neg_inf, fp16_neg_qnan_0) == (fp16_neg_qnan_0 | fp16_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp16_neg_inf, fp16_neg_snan_0) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_pos_qnan_0, fp16_pos_qnan_1) == (fp16_pos_qnan_0 | fp16_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp16_pos_qnan_0, fp16_pos_qnan_default) == (fp16_pos_qnan_0 | fp16_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp16_pos_qnan_0, fp16_pos_inf) == (fp16_pos_qnan_0 | fp16_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp16_pos_qnan_0, fp16_pos_snan_0) == (fp16_pos_qnan_0 | fp16_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_neg_qnan_0, fp16_neg_qnan_1) == (fp16_neg_qnan_0 | fp16_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp16_neg_qnan_0, fp16_neg_qnan_default) == (fp16_neg_qnan_0 | fp16_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp16_neg_qnan_0, fp16_neg_inf) == (fp16_neg_qnan_0 | fp16_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp16_neg_qnan_0, fp16_neg_snan_0) == (fp16_neg_qnan_0 | fp16_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_pos_snan_0, fp16_pos_snan_1) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_pos_snan_0, fp16_pos_qnan_0) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_pos_snan_0, fp16_pos_qnan_default) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_pos_snan_0, fp16_pos_inf) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_pos_snan_0, fp16_pos_qnan_0) == (fp16_pos_snan_0 | fp16_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_neg_snan_0, fp16_neg_snan_1) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_neg_snan_0, fp16_neg_qnan_0) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_neg_snan_0, fp16_neg_qnan_default) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_neg_snan_0, fp16_neg_inf) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp16_neg_snan_0, fp16_neg_qnan_0) == (fp16_neg_snan_0 | fp16_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp16_pos_normal_add_2_op_0, fp16_pos_normal_add_2_op_1) == (fp16_pos_normal_add_2_sum, fp_eflag_none));
  assert(float_add (fp16_pos_normal_add_3_op_0, fp16_pos_normal_add_3_op_1) == (fp16_pos_normal_add_3_sum, fp_eflag_none));
  assert(float_add (fp16_neg_normal_add_4_op_0, fp16_neg_normal_add_4_op_1) == (fp16_neg_normal_add_4_sum, fp_eflag_none));
  assert(float_add (fp16_neg_normal_add_5_op_0, fp16_neg_normal_add_5_op_1) == (fp16_neg_normal_add_5_sum, fp_eflag_none));

  float_set_rounding (fp_rounding_rne);

  assert(float_add (fp16_pos_normal_add_6_op_0, fp16_pos_normal_add_6_op_1) == (fp16_pos_normal_add_6_sum_rne, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_7_op_0, fp16_neg_normal_add_7_op_1) == (fp16_neg_normal_add_7_sum_rne, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_8_op_0, fp16_pos_normal_add_8_op_1) == (fp16_pos_normal_add_8_sum_rne, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_9_op_0, fp16_neg_normal_add_9_op_1) == (fp16_neg_normal_add_9_sum_rne, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_10_op_0, fp16_pos_normal_add_10_op_1) == (fp16_pos_normal_add_10_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_neg_normal_add_11_op_0, fp16_neg_normal_add_11_op_1) == (fp16_neg_normal_add_11_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_pos_normal_add_12_op_0, fp16_pos_normal_add_12_op_1) == (fp16_pos_normal_add_12_sum_rne, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_13_op_0, fp16_neg_normal_add_13_op_1) == (fp16_neg_normal_add_13_sum_rne, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rna);

  assert(float_add (fp16_pos_normal_add_6_op_0, fp16_pos_normal_add_6_op_1) == (fp16_pos_normal_add_6_sum_rna, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_7_op_0, fp16_neg_normal_add_7_op_1) == (fp16_neg_normal_add_7_sum_rna, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_8_op_0, fp16_pos_normal_add_8_op_1) == (fp16_pos_normal_add_8_sum_rna, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_9_op_0, fp16_neg_normal_add_9_op_1) == (fp16_neg_normal_add_9_sum_rna, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_10_op_0, fp16_pos_normal_add_10_op_1) == (fp16_pos_normal_add_10_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_neg_normal_add_11_op_0, fp16_neg_normal_add_11_op_1) == (fp16_neg_normal_add_11_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_pos_normal_add_12_op_0, fp16_pos_normal_add_12_op_1) == (fp16_pos_normal_add_12_sum_rna, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_13_op_0, fp16_neg_normal_add_13_op_1) == (fp16_neg_normal_add_13_sum_rna, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rdn);

  assert(float_add (fp16_pos_normal_add_6_op_0, fp16_pos_normal_add_6_op_1) == (fp16_pos_normal_add_6_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_7_op_0, fp16_neg_normal_add_7_op_1) == (fp16_neg_normal_add_7_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_8_op_0, fp16_pos_normal_add_8_op_1) == (fp16_pos_normal_add_8_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_9_op_0, fp16_neg_normal_add_9_op_1) == (fp16_neg_normal_add_9_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_10_op_0, fp16_pos_normal_add_10_op_1) == (fp16_pos_normal_add_10_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_neg_normal_add_11_op_0, fp16_neg_normal_add_11_op_1) == (fp16_neg_normal_add_11_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_pos_normal_add_12_op_0, fp16_pos_normal_add_12_op_1) == (fp16_pos_normal_add_12_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_13_op_0, fp16_neg_normal_add_13_op_1) == (fp16_neg_normal_add_13_sum_rdn, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rup);

  assert(float_add (fp16_pos_normal_add_6_op_0, fp16_pos_normal_add_6_op_1) == (fp16_pos_normal_add_6_sum_rup, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_7_op_0, fp16_neg_normal_add_7_op_1) == (fp16_neg_normal_add_7_sum_rup, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_8_op_0, fp16_pos_normal_add_8_op_1) == (fp16_pos_normal_add_8_sum_rup, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_9_op_0, fp16_neg_normal_add_9_op_1) == (fp16_neg_normal_add_9_sum_rup, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_10_op_0, fp16_pos_normal_add_10_op_1) == (fp16_pos_normal_add_10_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_neg_normal_add_11_op_0, fp16_neg_normal_add_11_op_1) == (fp16_neg_normal_add_11_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_pos_normal_add_12_op_0, fp16_pos_normal_add_12_op_1) == (fp16_pos_normal_add_12_sum_rup, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_13_op_0, fp16_neg_normal_add_13_op_1) == (fp16_neg_normal_add_13_sum_rup, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rtz);

  assert(float_add (fp16_pos_normal_add_6_op_0, fp16_pos_normal_add_6_op_1) == (fp16_pos_normal_add_6_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_7_op_0, fp16_neg_normal_add_7_op_1) == (fp16_neg_normal_add_7_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_8_op_0, fp16_pos_normal_add_8_op_1) == (fp16_pos_normal_add_8_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_9_op_0, fp16_neg_normal_add_9_op_1) == (fp16_neg_normal_add_9_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp16_pos_normal_add_10_op_0, fp16_pos_normal_add_10_op_1) == (fp16_pos_normal_add_10_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_neg_normal_add_11_op_0, fp16_neg_normal_add_11_op_1) == (fp16_neg_normal_add_11_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp16_pos_normal_add_12_op_0, fp16_pos_normal_add_12_op_1) == (fp16_pos_normal_add_12_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp16_neg_normal_add_13_op_0, fp16_neg_normal_add_13_op_1) == (fp16_neg_normal_add_13_sum_rtz, fp_eflag_inexact));

  float_set_rounding (fp_rounding_default);

  assert(float_add (fp16_pos_diff_exp_add_0_op_0, fp16_pos_diff_exp_add_0_op_1) == (fp16_pos_diff_exp_add_0_sum, fp_eflag_invalid));
  assert(float_add (fp16_neg_diff_exp_add_0_op_0, fp16_neg_diff_exp_add_0_op_1) == (fp16_neg_diff_exp_add_0_sum, fp_eflag_none));
  assert(float_add (fp16_pos_diff_exp_add_1_op_0, fp16_pos_diff_exp_add_1_op_1) == (fp16_pos_diff_exp_add_1_sum, fp_eflag_none));
  assert(float_add (fp16_neg_diff_exp_add_1_op_0, fp16_neg_diff_exp_add_1_op_1) == (fp16_neg_diff_exp_add_1_sum, fp_eflag_none));

  /* Single floating point */
  assert(float_add (fp32_pos_subnormal_add_0_op_0, fp32_pos_subnormal_add_0_op_1) == (fp32_pos_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp32_pos_subnormal_add_1_op_0, fp32_pos_subnormal_add_1_op_1) == (fp32_pos_subnormal_add_1_sum, fp_eflag_none));
  assert(float_add (fp32_neg_subnormal_add_0_op_0, fp32_neg_subnormal_add_0_op_1) == (fp32_neg_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp32_neg_subnormal_add_1_op_0, fp32_neg_subnormal_add_1_op_1) == (fp32_neg_subnormal_add_1_sum, fp_eflag_none));

  assert(float_add (fp32_pos_inf, fp32_pos_inf) == (fp32_pos_inf, fp_eflag_none));
  assert(float_add (fp32_pos_inf, fp32_pos_qnan_default) == (fp32_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp32_pos_inf, fp32_pos_qnan_0) == (fp32_pos_qnan_0 | fp32_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp32_pos_inf, fp32_pos_snan_0) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_neg_inf, fp32_neg_inf) == (fp32_neg_inf, fp_eflag_none));
  assert(float_add (fp32_neg_inf, fp32_neg_qnan_default) == (fp32_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp32_neg_inf, fp32_neg_qnan_0) == (fp32_neg_qnan_0 | fp32_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp32_neg_inf, fp32_neg_snan_0) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_pos_qnan_0, fp32_pos_qnan_1) == (fp32_pos_qnan_0 | fp32_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp32_pos_qnan_0, fp32_pos_qnan_default) == (fp32_pos_qnan_0 | fp32_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp32_pos_qnan_0, fp32_pos_inf) == (fp32_pos_qnan_0 | fp32_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp32_pos_qnan_0, fp32_pos_snan_0) == (fp32_pos_qnan_0 | fp32_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_neg_qnan_0, fp32_neg_qnan_1) == (fp32_neg_qnan_0 | fp32_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp32_neg_qnan_0, fp32_neg_qnan_default) == (fp32_neg_qnan_0 | fp32_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp32_neg_qnan_0, fp32_neg_inf) == (fp32_neg_qnan_0 | fp32_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp32_neg_qnan_0, fp32_neg_snan_0) == (fp32_neg_qnan_0 | fp32_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_pos_snan_0, fp32_pos_snan_1) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_pos_snan_0, fp32_pos_qnan_0) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_pos_snan_0, fp32_pos_qnan_default) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_pos_snan_0, fp32_pos_inf) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_pos_snan_0, fp32_pos_qnan_0) == (fp32_pos_snan_0 | fp32_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_neg_snan_0, fp32_neg_snan_1) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_neg_snan_0, fp32_neg_qnan_0) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_neg_snan_0, fp32_neg_qnan_default) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_neg_snan_0, fp32_neg_inf) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp32_neg_snan_0, fp32_neg_qnan_0) == (fp32_neg_snan_0 | fp32_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp32_pos_normal_add_2_op_0, fp32_pos_normal_add_2_op_1) == (fp32_pos_normal_add_2_sum, fp_eflag_none));
  assert(float_add (fp32_pos_normal_add_3_op_0, fp32_pos_normal_add_3_op_1) == (fp32_pos_normal_add_3_sum, fp_eflag_none));
  assert(float_add (fp32_neg_normal_add_4_op_0, fp32_neg_normal_add_4_op_1) == (fp32_neg_normal_add_4_sum, fp_eflag_none));
  assert(float_add (fp32_neg_normal_add_5_op_0, fp32_neg_normal_add_5_op_1) == (fp32_neg_normal_add_5_sum, fp_eflag_none));

  float_set_rounding (fp_rounding_rne);

  assert(float_add (fp32_pos_normal_add_6_op_0, fp32_pos_normal_add_6_op_1) == (fp32_pos_normal_add_6_sum_rne, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_7_op_0, fp32_neg_normal_add_7_op_1) == (fp32_neg_normal_add_7_sum_rne, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_8_op_0, fp32_pos_normal_add_8_op_1) == (fp32_pos_normal_add_8_sum_rne, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_9_op_0, fp32_neg_normal_add_9_op_1) == (fp32_neg_normal_add_9_sum_rne, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_10_op_0, fp32_pos_normal_add_10_op_1) == (fp32_pos_normal_add_10_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_neg_normal_add_11_op_0, fp32_neg_normal_add_11_op_1) == (fp32_neg_normal_add_11_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_pos_normal_add_12_op_0, fp32_pos_normal_add_12_op_1) == (fp32_pos_normal_add_12_sum_rne, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_13_op_0, fp32_neg_normal_add_13_op_1) == (fp32_neg_normal_add_13_sum_rne, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rna);

  assert(float_add (fp32_pos_normal_add_6_op_0, fp32_pos_normal_add_6_op_1) == (fp32_pos_normal_add_6_sum_rna, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_7_op_0, fp32_neg_normal_add_7_op_1) == (fp32_neg_normal_add_7_sum_rna, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_8_op_0, fp32_pos_normal_add_8_op_1) == (fp32_pos_normal_add_8_sum_rna, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_9_op_0, fp32_neg_normal_add_9_op_1) == (fp32_neg_normal_add_9_sum_rna, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_10_op_0, fp32_pos_normal_add_10_op_1) == (fp32_pos_normal_add_10_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_neg_normal_add_11_op_0, fp32_neg_normal_add_11_op_1) == (fp32_neg_normal_add_11_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_pos_normal_add_12_op_0, fp32_pos_normal_add_12_op_1) == (fp32_pos_normal_add_12_sum_rna, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_13_op_0, fp32_neg_normal_add_13_op_1) == (fp32_neg_normal_add_13_sum_rna, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rdn);

  assert(float_add (fp32_pos_normal_add_6_op_0, fp32_pos_normal_add_6_op_1) == (fp32_pos_normal_add_6_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_7_op_0, fp32_neg_normal_add_7_op_1) == (fp32_neg_normal_add_7_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_8_op_0, fp32_pos_normal_add_8_op_1) == (fp32_pos_normal_add_8_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_9_op_0, fp32_neg_normal_add_9_op_1) == (fp32_neg_normal_add_9_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_10_op_0, fp32_pos_normal_add_10_op_1) == (fp32_pos_normal_add_10_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_neg_normal_add_11_op_0, fp32_neg_normal_add_11_op_1) == (fp32_neg_normal_add_11_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_pos_normal_add_12_op_0, fp32_pos_normal_add_12_op_1) == (fp32_pos_normal_add_12_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_13_op_0, fp32_neg_normal_add_13_op_1) == (fp32_neg_normal_add_13_sum_rdn, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rup);

  assert(float_add (fp32_pos_normal_add_6_op_0, fp32_pos_normal_add_6_op_1) == (fp32_pos_normal_add_6_sum_rup, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_7_op_0, fp32_neg_normal_add_7_op_1) == (fp32_neg_normal_add_7_sum_rup, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_8_op_0, fp32_pos_normal_add_8_op_1) == (fp32_pos_normal_add_8_sum_rup, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_9_op_0, fp32_neg_normal_add_9_op_1) == (fp32_neg_normal_add_9_sum_rup, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_10_op_0, fp32_pos_normal_add_10_op_1) == (fp32_pos_normal_add_10_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_neg_normal_add_11_op_0, fp32_neg_normal_add_11_op_1) == (fp32_neg_normal_add_11_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_pos_normal_add_12_op_0, fp32_pos_normal_add_12_op_1) == (fp32_pos_normal_add_12_sum_rup, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_13_op_0, fp32_neg_normal_add_13_op_1) == (fp32_neg_normal_add_13_sum_rup, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rtz);

  assert(float_add (fp32_pos_normal_add_6_op_0, fp32_pos_normal_add_6_op_1) == (fp32_pos_normal_add_6_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_7_op_0, fp32_neg_normal_add_7_op_1) == (fp32_neg_normal_add_7_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_8_op_0, fp32_pos_normal_add_8_op_1) == (fp32_pos_normal_add_8_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_9_op_0, fp32_neg_normal_add_9_op_1) == (fp32_neg_normal_add_9_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp32_pos_normal_add_10_op_0, fp32_pos_normal_add_10_op_1) == (fp32_pos_normal_add_10_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_neg_normal_add_11_op_0, fp32_neg_normal_add_11_op_1) == (fp32_neg_normal_add_11_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp32_pos_normal_add_12_op_0, fp32_pos_normal_add_12_op_1) == (fp32_pos_normal_add_12_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp32_neg_normal_add_13_op_0, fp32_neg_normal_add_13_op_1) == (fp32_neg_normal_add_13_sum_rtz, fp_eflag_inexact));

  float_set_rounding (fp_rounding_default);

  assert(float_add (fp32_pos_diff_exp_add_0_op_0, fp32_pos_diff_exp_add_0_op_1) == (fp32_pos_diff_exp_add_0_sum, fp_eflag_invalid));
  assert(float_add (fp32_neg_diff_exp_add_0_op_0, fp32_neg_diff_exp_add_0_op_1) == (fp32_neg_diff_exp_add_0_sum, fp_eflag_none));
  assert(float_add (fp32_pos_diff_exp_add_1_op_0, fp32_pos_diff_exp_add_1_op_1) == (fp32_pos_diff_exp_add_1_sum, fp_eflag_none));
  assert(float_add (fp32_neg_diff_exp_add_1_op_0, fp32_neg_diff_exp_add_1_op_1) == (fp32_neg_diff_exp_add_1_sum, fp_eflag_none));

  /* Double floating point */
  assert(float_add (fp64_pos_subnormal_add_0_op_0, fp64_pos_subnormal_add_0_op_1) == (fp64_pos_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp64_pos_subnormal_add_1_op_0, fp64_pos_subnormal_add_1_op_1) == (fp64_pos_subnormal_add_1_sum, fp_eflag_none));
  assert(float_add (fp64_neg_subnormal_add_0_op_0, fp64_neg_subnormal_add_0_op_1) == (fp64_neg_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp64_neg_subnormal_add_1_op_0, fp64_neg_subnormal_add_1_op_1) == (fp64_neg_subnormal_add_1_sum, fp_eflag_none));

  assert(float_add (fp64_pos_inf, fp64_pos_inf) == (fp64_pos_inf, fp_eflag_none));
  assert(float_add (fp64_pos_inf, fp64_pos_qnan_default) == (fp64_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp64_pos_inf, fp64_pos_qnan_0) == (fp64_pos_qnan_0 | fp64_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp64_pos_inf, fp64_pos_snan_0) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_neg_inf, fp64_neg_inf) == (fp64_neg_inf, fp_eflag_none));
  assert(float_add (fp64_neg_inf, fp64_neg_qnan_default) == (fp64_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp64_neg_inf, fp64_neg_qnan_0) == (fp64_neg_qnan_0 | fp64_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp64_neg_inf, fp64_neg_snan_0) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_pos_qnan_0, fp64_pos_qnan_1) == (fp64_pos_qnan_0 | fp64_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp64_pos_qnan_0, fp64_pos_qnan_default) == (fp64_pos_qnan_0 | fp64_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp64_pos_qnan_0, fp64_pos_inf) == (fp64_pos_qnan_0 | fp64_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp64_pos_qnan_0, fp64_pos_snan_0) == (fp64_pos_qnan_0 | fp64_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_neg_qnan_0, fp64_neg_qnan_1) == (fp64_neg_qnan_0 | fp64_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp64_neg_qnan_0, fp64_neg_qnan_default) == (fp64_neg_qnan_0 | fp64_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp64_neg_qnan_0, fp64_neg_inf) == (fp64_neg_qnan_0 | fp64_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp64_neg_qnan_0, fp64_neg_snan_0) == (fp64_neg_qnan_0 | fp64_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_pos_snan_0, fp64_pos_snan_1) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_pos_snan_0, fp64_pos_qnan_0) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_pos_snan_0, fp64_pos_qnan_default) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_pos_snan_0, fp64_pos_inf) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_pos_snan_0, fp64_pos_qnan_0) == (fp64_pos_snan_0 | fp64_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_neg_snan_0, fp64_neg_snan_1) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_neg_snan_0, fp64_neg_qnan_0) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_neg_snan_0, fp64_neg_qnan_default) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_neg_snan_0, fp64_neg_inf) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp64_neg_snan_0, fp64_neg_qnan_0) == (fp64_neg_snan_0 | fp64_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp64_pos_normal_add_2_op_0, fp64_pos_normal_add_2_op_1) == (fp64_pos_normal_add_2_sum, fp_eflag_none));
  assert(float_add (fp64_pos_normal_add_3_op_0, fp64_pos_normal_add_3_op_1) == (fp64_pos_normal_add_3_sum, fp_eflag_none));
  assert(float_add (fp64_neg_normal_add_4_op_0, fp64_neg_normal_add_4_op_1) == (fp64_neg_normal_add_4_sum, fp_eflag_none));
  assert(float_add (fp64_neg_normal_add_5_op_0, fp64_neg_normal_add_5_op_1) == (fp64_neg_normal_add_5_sum, fp_eflag_none));

  float_set_rounding (fp_rounding_rne);

  assert(float_add (fp64_pos_normal_add_6_op_0, fp64_pos_normal_add_6_op_1) == (fp64_pos_normal_add_6_sum_rne, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_7_op_0, fp64_neg_normal_add_7_op_1) == (fp64_neg_normal_add_7_sum_rne, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_8_op_0, fp64_pos_normal_add_8_op_1) == (fp64_pos_normal_add_8_sum_rne, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_9_op_0, fp64_neg_normal_add_9_op_1) == (fp64_neg_normal_add_9_sum_rne, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_10_op_0, fp64_pos_normal_add_10_op_1) == (fp64_pos_normal_add_10_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_neg_normal_add_11_op_0, fp64_neg_normal_add_11_op_1) == (fp64_neg_normal_add_11_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_pos_normal_add_12_op_0, fp64_pos_normal_add_12_op_1) == (fp64_pos_normal_add_12_sum_rne, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_13_op_0, fp64_neg_normal_add_13_op_1) == (fp64_neg_normal_add_13_sum_rne, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rna);

  assert(float_add (fp64_pos_normal_add_6_op_0, fp64_pos_normal_add_6_op_1) == (fp64_pos_normal_add_6_sum_rna, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_7_op_0, fp64_neg_normal_add_7_op_1) == (fp64_neg_normal_add_7_sum_rna, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_8_op_0, fp64_pos_normal_add_8_op_1) == (fp64_pos_normal_add_8_sum_rna, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_9_op_0, fp64_neg_normal_add_9_op_1) == (fp64_neg_normal_add_9_sum_rna, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_10_op_0, fp64_pos_normal_add_10_op_1) == (fp64_pos_normal_add_10_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_neg_normal_add_11_op_0, fp64_neg_normal_add_11_op_1) == (fp64_neg_normal_add_11_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_pos_normal_add_12_op_0, fp64_pos_normal_add_12_op_1) == (fp64_pos_normal_add_12_sum_rna, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_13_op_0, fp64_neg_normal_add_13_op_1) == (fp64_neg_normal_add_13_sum_rna, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rdn);

  assert(float_add (fp64_pos_normal_add_6_op_0, fp64_pos_normal_add_6_op_1) == (fp64_pos_normal_add_6_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_7_op_0, fp64_neg_normal_add_7_op_1) == (fp64_neg_normal_add_7_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_8_op_0, fp64_pos_normal_add_8_op_1) == (fp64_pos_normal_add_8_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_9_op_0, fp64_neg_normal_add_9_op_1) == (fp64_neg_normal_add_9_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_10_op_0, fp64_pos_normal_add_10_op_1) == (fp64_pos_normal_add_10_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_neg_normal_add_11_op_0, fp64_neg_normal_add_11_op_1) == (fp64_neg_normal_add_11_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_pos_normal_add_12_op_0, fp64_pos_normal_add_12_op_1) == (fp64_pos_normal_add_12_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_13_op_0, fp64_neg_normal_add_13_op_1) == (fp64_neg_normal_add_13_sum_rdn, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rup);

  assert(float_add (fp64_pos_normal_add_6_op_0, fp64_pos_normal_add_6_op_1) == (fp64_pos_normal_add_6_sum_rup, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_7_op_0, fp64_neg_normal_add_7_op_1) == (fp64_neg_normal_add_7_sum_rup, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_8_op_0, fp64_pos_normal_add_8_op_1) == (fp64_pos_normal_add_8_sum_rup, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_9_op_0, fp64_neg_normal_add_9_op_1) == (fp64_neg_normal_add_9_sum_rup, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_10_op_0, fp64_pos_normal_add_10_op_1) == (fp64_pos_normal_add_10_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_neg_normal_add_11_op_0, fp64_neg_normal_add_11_op_1) == (fp64_neg_normal_add_11_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_pos_normal_add_12_op_0, fp64_pos_normal_add_12_op_1) == (fp64_pos_normal_add_12_sum_rup, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_13_op_0, fp64_neg_normal_add_13_op_1) == (fp64_neg_normal_add_13_sum_rup, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rtz);

  assert(float_add (fp64_pos_normal_add_6_op_0, fp64_pos_normal_add_6_op_1) == (fp64_pos_normal_add_6_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_7_op_0, fp64_neg_normal_add_7_op_1) == (fp64_neg_normal_add_7_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_8_op_0, fp64_pos_normal_add_8_op_1) == (fp64_pos_normal_add_8_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_9_op_0, fp64_neg_normal_add_9_op_1) == (fp64_neg_normal_add_9_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp64_pos_normal_add_10_op_0, fp64_pos_normal_add_10_op_1) == (fp64_pos_normal_add_10_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_neg_normal_add_11_op_0, fp64_neg_normal_add_11_op_1) == (fp64_neg_normal_add_11_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp64_pos_normal_add_12_op_0, fp64_pos_normal_add_12_op_1) == (fp64_pos_normal_add_12_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp64_neg_normal_add_13_op_0, fp64_neg_normal_add_13_op_1) == (fp64_neg_normal_add_13_sum_rtz, fp_eflag_inexact));

  float_set_rounding (fp_rounding_default);

  assert(float_add (fp64_pos_diff_exp_add_0_op_0, fp64_pos_diff_exp_add_0_op_1) == (fp64_pos_diff_exp_add_0_sum, fp_eflag_invalid));
  assert(float_add (fp64_neg_diff_exp_add_0_op_0, fp64_neg_diff_exp_add_0_op_1) == (fp64_neg_diff_exp_add_0_sum, fp_eflag_none));
  assert(float_add (fp64_pos_diff_exp_add_1_op_0, fp64_pos_diff_exp_add_1_op_1) == (fp64_pos_diff_exp_add_1_sum, fp_eflag_none));
  assert(float_add (fp64_neg_diff_exp_add_1_op_0, fp64_neg_diff_exp_add_1_op_1) == (fp64_neg_diff_exp_add_1_sum, fp_eflag_none));

  /* Quad floating point */
  assert(float_add (fp128_pos_subnormal_add_0_op_0, fp128_pos_subnormal_add_0_op_1) == (fp128_pos_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp128_pos_subnormal_add_1_op_0, fp128_pos_subnormal_add_1_op_1) == (fp128_pos_subnormal_add_1_sum, fp_eflag_none));
  assert(float_add (fp128_neg_subnormal_add_0_op_0, fp128_neg_subnormal_add_0_op_1) == (fp128_neg_subnormal_add_0_sum, fp_eflag_none));
  assert(float_add (fp128_neg_subnormal_add_1_op_0, fp128_neg_subnormal_add_1_op_1) == (fp128_neg_subnormal_add_1_sum, fp_eflag_none));

  assert(float_add (fp128_pos_inf, fp128_pos_inf) == (fp128_pos_inf, fp_eflag_none));
  assert(float_add (fp128_pos_inf, fp128_pos_qnan_default) == (fp128_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp128_pos_inf, fp128_pos_qnan_0) == (fp128_pos_qnan_0 | fp128_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp128_pos_inf, fp128_pos_snan_0) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_neg_inf, fp128_neg_inf) == (fp128_neg_inf, fp_eflag_none));
  assert(float_add (fp128_neg_inf, fp128_neg_qnan_default) == (fp128_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp128_neg_inf, fp128_neg_qnan_0) == (fp128_neg_qnan_0 | fp128_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp128_neg_inf, fp128_neg_snan_0) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_pos_qnan_0, fp128_pos_qnan_1) == (fp128_pos_qnan_0 | fp128_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp128_pos_qnan_0, fp128_pos_qnan_default) == (fp128_pos_qnan_0 | fp128_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp128_pos_qnan_0, fp128_pos_inf) == (fp128_pos_qnan_0 | fp128_pos_qnan_default, fp_eflag_none));
  assert(float_add (fp128_pos_qnan_0, fp128_pos_snan_0) == (fp128_pos_qnan_0 | fp128_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_neg_qnan_0, fp128_neg_qnan_1) == (fp128_neg_qnan_0 | fp128_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp128_neg_qnan_0, fp128_neg_qnan_default) == (fp128_neg_qnan_0 | fp128_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp128_neg_qnan_0, fp128_neg_inf) == (fp128_neg_qnan_0 | fp128_neg_qnan_default, fp_eflag_none));
  assert(float_add (fp128_neg_qnan_0, fp128_neg_snan_0) == (fp128_neg_qnan_0 | fp128_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_pos_snan_0, fp128_pos_snan_1) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_pos_snan_0, fp128_pos_qnan_0) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_pos_snan_0, fp128_pos_qnan_default) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_pos_snan_0, fp128_pos_inf) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_pos_snan_0, fp128_pos_qnan_0) == (fp128_pos_snan_0 | fp128_pos_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_neg_snan_0, fp128_neg_snan_1) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_neg_snan_0, fp128_neg_qnan_0) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_neg_snan_0, fp128_neg_qnan_default) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_neg_snan_0, fp128_neg_inf) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));
  assert(float_add (fp128_neg_snan_0, fp128_neg_qnan_0) == (fp128_neg_snan_0 | fp128_neg_qnan_default, fp_eflag_invalid));

  assert(float_add (fp128_pos_normal_add_2_op_0, fp128_pos_normal_add_2_op_1) == (fp128_pos_normal_add_2_sum, fp_eflag_none));
  assert(float_add (fp128_pos_normal_add_3_op_0, fp128_pos_normal_add_3_op_1) == (fp128_pos_normal_add_3_sum, fp_eflag_none));
  assert(float_add (fp128_neg_normal_add_4_op_0, fp128_neg_normal_add_4_op_1) == (fp128_neg_normal_add_4_sum, fp_eflag_none));
  assert(float_add (fp128_neg_normal_add_5_op_0, fp128_neg_normal_add_5_op_1) == (fp128_neg_normal_add_5_sum, fp_eflag_none));

  float_set_rounding (fp_rounding_rne);

  assert(float_add (fp128_pos_normal_add_6_op_0, fp128_pos_normal_add_6_op_1) == (fp128_pos_normal_add_6_sum_rne, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_7_op_0, fp128_neg_normal_add_7_op_1) == (fp128_neg_normal_add_7_sum_rne, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_8_op_0, fp128_pos_normal_add_8_op_1) == (fp128_pos_normal_add_8_sum_rne, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_9_op_0, fp128_neg_normal_add_9_op_1) == (fp128_neg_normal_add_9_sum_rne, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_10_op_0, fp128_pos_normal_add_10_op_1) == (fp128_pos_normal_add_10_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_neg_normal_add_11_op_0, fp128_neg_normal_add_11_op_1) == (fp128_neg_normal_add_11_sum_rne, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_pos_normal_add_12_op_0, fp128_pos_normal_add_12_op_1) == (fp128_pos_normal_add_12_sum_rne, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_13_op_0, fp128_neg_normal_add_13_op_1) == (fp128_neg_normal_add_13_sum_rne, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rna);

  assert(float_add (fp128_pos_normal_add_6_op_0, fp128_pos_normal_add_6_op_1) == (fp128_pos_normal_add_6_sum_rna, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_7_op_0, fp128_neg_normal_add_7_op_1) == (fp128_neg_normal_add_7_sum_rna, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_8_op_0, fp128_pos_normal_add_8_op_1) == (fp128_pos_normal_add_8_sum_rna, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_9_op_0, fp128_neg_normal_add_9_op_1) == (fp128_neg_normal_add_9_sum_rna, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_10_op_0, fp128_pos_normal_add_10_op_1) == (fp128_pos_normal_add_10_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_neg_normal_add_11_op_0, fp128_neg_normal_add_11_op_1) == (fp128_neg_normal_add_11_sum_rna, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_pos_normal_add_12_op_0, fp128_pos_normal_add_12_op_1) == (fp128_pos_normal_add_12_sum_rna, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_13_op_0, fp128_neg_normal_add_13_op_1) == (fp128_neg_normal_add_13_sum_rna, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rdn);

  assert(float_add (fp128_pos_normal_add_6_op_0, fp128_pos_normal_add_6_op_1) == (fp128_pos_normal_add_6_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_7_op_0, fp128_neg_normal_add_7_op_1) == (fp128_neg_normal_add_7_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_8_op_0, fp128_pos_normal_add_8_op_1) == (fp128_pos_normal_add_8_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_9_op_0, fp128_neg_normal_add_9_op_1) == (fp128_neg_normal_add_9_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_10_op_0, fp128_pos_normal_add_10_op_1) == (fp128_pos_normal_add_10_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_neg_normal_add_11_op_0, fp128_neg_normal_add_11_op_1) == (fp128_neg_normal_add_11_sum_rdn, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_pos_normal_add_12_op_0, fp128_pos_normal_add_12_op_1) == (fp128_pos_normal_add_12_sum_rdn, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_13_op_0, fp128_neg_normal_add_13_op_1) == (fp128_neg_normal_add_13_sum_rdn, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rup);

  assert(float_add (fp128_pos_normal_add_6_op_0, fp128_pos_normal_add_6_op_1) == (fp128_pos_normal_add_6_sum_rup, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_7_op_0, fp128_neg_normal_add_7_op_1) == (fp128_neg_normal_add_7_sum_rup, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_8_op_0, fp128_pos_normal_add_8_op_1) == (fp128_pos_normal_add_8_sum_rup, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_9_op_0, fp128_neg_normal_add_9_op_1) == (fp128_neg_normal_add_9_sum_rup, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_10_op_0, fp128_pos_normal_add_10_op_1) == (fp128_pos_normal_add_10_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_neg_normal_add_11_op_0, fp128_neg_normal_add_11_op_1) == (fp128_neg_normal_add_11_sum_rup, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_pos_normal_add_12_op_0, fp128_pos_normal_add_12_op_1) == (fp128_pos_normal_add_12_sum_rup, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_13_op_0, fp128_neg_normal_add_13_op_1) == (fp128_neg_normal_add_13_sum_rup, fp_eflag_inexact));

  float_set_rounding (fp_rounding_rtz);

  assert(float_add (fp128_pos_normal_add_6_op_0, fp128_pos_normal_add_6_op_1) == (fp128_pos_normal_add_6_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_7_op_0, fp128_neg_normal_add_7_op_1) == (fp128_neg_normal_add_7_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_8_op_0, fp128_pos_normal_add_8_op_1) == (fp128_pos_normal_add_8_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_9_op_0, fp128_neg_normal_add_9_op_1) == (fp128_neg_normal_add_9_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp128_pos_normal_add_10_op_0, fp128_pos_normal_add_10_op_1) == (fp128_pos_normal_add_10_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_neg_normal_add_11_op_0, fp128_neg_normal_add_11_op_1) == (fp128_neg_normal_add_11_sum_rtz, fp_eflag_overflow_and_inexact));
  assert(float_add (fp128_pos_normal_add_12_op_0, fp128_pos_normal_add_12_op_1) == (fp128_pos_normal_add_12_sum_rtz, fp_eflag_inexact));
  assert(float_add (fp128_neg_normal_add_13_op_0, fp128_neg_normal_add_13_op_1) == (fp128_neg_normal_add_13_sum_rtz, fp_eflag_inexact));

  float_set_rounding (fp_rounding_default);

  assert(float_add (fp128_pos_diff_exp_add_0_op_0, fp128_pos_diff_exp_add_0_op_1) == (fp128_pos_diff_exp_add_0_sum, fp_eflag_invalid));
  assert(float_add (fp128_neg_diff_exp_add_0_op_0, fp128_neg_diff_exp_add_0_op_1) == (fp128_neg_diff_exp_add_0_sum, fp_eflag_none));
  assert(float_add (fp128_pos_diff_exp_add_1_op_0, fp128_pos_diff_exp_add_1_op_1) == (fp128_pos_diff_exp_add_1_sum, fp_eflag_none));
  assert(float_add (fp128_neg_diff_exp_add_1_op_0, fp128_neg_diff_exp_add_1_op_1) == (fp128_neg_diff_exp_add_1_sum, fp_eflag_none));
}

function main () -> unit = {
  test_float_add ();
}
