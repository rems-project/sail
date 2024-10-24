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
$include <float/nan.sail>
$include "data.sail"

function test_float_is_nan () -> unit = {
  /* Half floating point */
  assert(float_is_nan(fp16_pos_snan_0));
  assert(float_is_nan(fp16_pos_snan_1));
  assert(float_is_nan(fp16_pos_qnan_0));
  assert(float_is_nan(fp16_pos_qnan_1));

  assert(float_is_nan(fp16_neg_snan_0));
  assert(float_is_nan(fp16_neg_snan_1));
  assert(float_is_nan(fp16_neg_qnan_0));
  assert(float_is_nan(fp16_neg_qnan_1));

  assert(float_is_nan(fp16_pos_inf) == false);
  assert(float_is_nan(fp16_neg_zero) == false);
  assert(float_is_nan(fp16_pos_denormal_0) == false);
  assert(float_is_nan(fp16_pos_denormal_1) == false);
  assert(float_is_nan(fp16_neg_normal_0) == false);
  assert(float_is_nan(fp16_neg_normal_1) == false);

  /* Single floating point */
  assert(float_is_nan(fp32_pos_snan_0));
  assert(float_is_nan(fp32_pos_snan_1));
  assert(float_is_nan(fp32_pos_qnan_0));
  assert(float_is_nan(fp32_pos_qnan_1));

  assert(float_is_nan(fp32_neg_snan_0));
  assert(float_is_nan(fp32_neg_snan_1));
  assert(float_is_nan(fp32_neg_qnan_0));
  assert(float_is_nan(fp32_neg_qnan_1));

  assert(float_is_nan(fp32_pos_inf) == false);
  assert(float_is_nan(fp32_neg_zero) == false);
  assert(float_is_nan(fp32_pos_denormal_0) == false);
  assert(float_is_nan(fp32_pos_denormal_1) == false);
  assert(float_is_nan(fp32_neg_normal_0) == false);
  assert(float_is_nan(fp32_neg_normal_1) == false);

  /* Double floating point */
  assert(float_is_nan(fp64_pos_snan_0));
  assert(float_is_nan(fp64_pos_snan_1));
  assert(float_is_nan(fp64_pos_qnan_0));
  assert(float_is_nan(fp64_pos_qnan_1));

  assert(float_is_nan(fp64_neg_snan_0));
  assert(float_is_nan(fp64_neg_snan_1));
  assert(float_is_nan(fp64_neg_qnan_0));
  assert(float_is_nan(fp64_neg_qnan_1));

  assert(float_is_nan(fp64_pos_inf) == false);
  assert(float_is_nan(fp64_neg_zero) == false);
  assert(float_is_nan(fp64_pos_denormal_0) == false);
  assert(float_is_nan(fp64_pos_denormal_1) == false);
  assert(float_is_nan(fp64_neg_normal_0) == false);
  assert(float_is_nan(fp64_neg_normal_1) == false);

  /* Quad floating point */
  assert(float_is_nan(fp128_pos_snan_0));
  assert(float_is_nan(fp128_pos_snan_1));
  assert(float_is_nan(fp128_pos_qnan_0));
  assert(float_is_nan(fp128_pos_qnan_1));

  assert(float_is_nan(fp128_neg_snan_0));
  assert(float_is_nan(fp128_neg_snan_1));
  assert(float_is_nan(fp128_neg_qnan_0));
  assert(float_is_nan(fp128_neg_qnan_1));

  assert(float_is_nan(fp128_pos_inf) == false);
  assert(float_is_nan(fp128_neg_zero) == false);
  assert(float_is_nan(fp128_pos_denormal_0) == false);
  assert(float_is_nan(fp128_pos_denormal_1) == false);
  assert(float_is_nan(fp128_neg_normal_0) == false);
  assert(float_is_nan(fp128_neg_normal_1) == false);
}

function test_float_is_snan () -> unit = {
  /* Half floating point */
  assert(float_is_snan(fp16_pos_snan_0));
  assert(float_is_snan(fp16_pos_snan_1));
  assert(float_is_snan(fp16_neg_snan_0));
  assert(float_is_snan(fp16_neg_snan_1));

  assert(float_is_snan(fp16_pos_inf) == false);
  assert(float_is_snan(fp16_neg_zero) == false);
  assert(float_is_snan(fp16_pos_qnan_0) == false);
  assert(float_is_snan(fp16_neg_qnan_0) == false);
  assert(float_is_snan(fp16_pos_denormal_0) == false);
  assert(float_is_snan(fp16_neg_normal_0) == false);

  /* Single floating point */
  assert(float_is_snan(fp32_pos_snan_0));
  assert(float_is_snan(fp32_pos_snan_1));
  assert(float_is_snan(fp32_neg_snan_0));
  assert(float_is_snan(fp32_neg_snan_1));

  assert(float_is_snan(fp32_pos_inf) == false);
  assert(float_is_snan(fp32_neg_zero) == false);
  assert(float_is_snan(fp32_pos_qnan_0) == false);
  assert(float_is_snan(fp32_neg_qnan_0) == false);
  assert(float_is_snan(fp32_pos_denormal_0) == false);
  assert(float_is_snan(fp32_neg_normal_0) == false);

  /* Double floating point */
  assert(float_is_snan(fp64_pos_snan_0));
  assert(float_is_snan(fp64_pos_snan_1));
  assert(float_is_snan(fp64_neg_snan_0));
  assert(float_is_snan(fp64_neg_snan_1));

  assert(float_is_snan(fp64_pos_inf) == false);
  assert(float_is_snan(fp64_neg_zero) == false);
  assert(float_is_snan(fp64_pos_qnan_0) == false);
  assert(float_is_snan(fp64_neg_qnan_0) == false);
  assert(float_is_snan(fp64_pos_denormal_0) == false);
  assert(float_is_snan(fp64_neg_normal_0) == false);

  /* Quad floating point */
  assert(float_is_snan(fp128_pos_snan_0));
  assert(float_is_snan(fp128_pos_snan_1));
  assert(float_is_snan(fp128_neg_snan_0));
  assert(float_is_snan(fp128_neg_snan_1));

  assert(float_is_snan(fp128_pos_inf) == false);
  assert(float_is_snan(fp128_neg_zero) == false);
  assert(float_is_snan(fp128_pos_qnan_0) == false);
  assert(float_is_snan(fp128_neg_qnan_0) == false);
  assert(float_is_snan(fp128_pos_denormal_0) == false);
  assert(float_is_snan(fp128_neg_normal_0) == false);
}

function test_float_is_qnan () -> unit = {
  /* Half floating point */
  assert(float_is_qnan(fp16_pos_qnan_0));
  assert(float_is_qnan(fp16_pos_qnan_1));
  assert(float_is_qnan(fp16_neg_qnan_0));
  assert(float_is_qnan(fp16_neg_qnan_1));

  assert(float_is_qnan(fp16_pos_inf) == false);
  assert(float_is_qnan(fp16_neg_zero) == false);
  assert(float_is_qnan(fp16_pos_snan_0) == false);
  assert(float_is_qnan(fp16_neg_snan_0) == false);
  assert(float_is_qnan(fp16_pos_denormal_0) == false);
  assert(float_is_qnan(fp16_neg_normal_0) == false);

  /* Single floating pont */
  assert(float_is_qnan(fp32_pos_qnan_0));
  assert(float_is_qnan(fp32_pos_qnan_1));
  assert(float_is_qnan(fp32_neg_qnan_0));
  assert(float_is_qnan(fp32_neg_qnan_1));

  assert(float_is_qnan(fp32_pos_inf) == false);
  assert(float_is_qnan(fp32_neg_zero) == false);
  assert(float_is_qnan(fp32_pos_snan_0) == false);
  assert(float_is_qnan(fp32_neg_snan_0) == false);
  assert(float_is_qnan(fp32_pos_denormal_0) == false);
  assert(float_is_qnan(fp32_neg_normal_0) == false);

  /* Double floating point */
  assert(float_is_qnan(fp64_pos_qnan_0));
  assert(float_is_qnan(fp64_pos_qnan_1));
  assert(float_is_qnan(fp64_neg_qnan_0));
  assert(float_is_qnan(fp64_neg_qnan_1));

  assert(float_is_qnan(fp64_pos_inf) == false);
  assert(float_is_qnan(fp64_neg_zero) == false);
  assert(float_is_qnan(fp64_pos_snan_0) == false);
  assert(float_is_qnan(fp64_neg_snan_0) == false);
  assert(float_is_qnan(fp64_pos_denormal_0) == false);
  assert(float_is_qnan(fp64_neg_normal_0) == false);

  /* Quad floating point */
  assert(float_is_qnan(fp128_pos_qnan_0));
  assert(float_is_qnan(fp128_pos_qnan_1));
  assert(float_is_qnan(fp128_neg_qnan_0));
  assert(float_is_qnan(fp128_neg_qnan_1));

  assert(float_is_qnan(fp128_pos_inf) == false);
  assert(float_is_qnan(fp128_neg_zero) == false);
  assert(float_is_qnan(fp128_pos_snan_0) == false);
  assert(float_is_qnan(fp128_neg_snan_0) == false);
  assert(float_is_qnan(fp128_pos_denormal_0) == false);
  assert(float_is_qnan(fp128_neg_normal_0) == false);
}

function main () -> unit = {
  test_float_is_nan();
  test_float_is_snan();
  test_float_is_qnan();
}
