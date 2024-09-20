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
$include <float/sign.sail>
$include "data.sail"

function test_float_is_positive () -> unit = {
  /* Half floating point */
  assert(float_is_positive(fp16_pos_snan_0));
  assert(float_is_positive(fp16_pos_qnan_0));
  assert(float_is_positive(fp16_pos_zero));
  assert(float_is_positive(fp16_pos_inf));
  assert(float_is_positive(fp16_pos_denormal_0));
  assert(float_is_positive(fp16_pos_normal_0));

  assert(float_is_positive(fp16_neg_snan_0) == false);
  assert(float_is_positive(fp16_neg_qnan_0) == false);
  assert(float_is_positive(fp16_neg_zero) == false);
  assert(float_is_positive(fp16_neg_inf) == false);
  assert(float_is_positive(fp16_neg_denormal_0) == false);
  assert(float_is_positive(fp16_neg_normal_0) == false);

  /* Single floating point */
  assert(float_is_positive(fp32_pos_snan_0));
  assert(float_is_positive(fp32_pos_qnan_0));
  assert(float_is_positive(fp32_pos_zero));
  assert(float_is_positive(fp32_pos_inf));
  assert(float_is_positive(fp32_pos_denormal_0));
  assert(float_is_positive(fp32_pos_normal_0));

  assert(float_is_positive(fp32_neg_snan_0) == false);
  assert(float_is_positive(fp32_neg_qnan_0) == false);
  assert(float_is_positive(fp32_neg_zero) == false);
  assert(float_is_positive(fp32_neg_inf) == false);
  assert(float_is_positive(fp32_neg_denormal_0) == false);
  assert(float_is_positive(fp32_neg_normal_0) == false);

  /* Double floating point */
  assert(float_is_positive(fp64_pos_snan_0));
  assert(float_is_positive(fp64_pos_qnan_0));
  assert(float_is_positive(fp64_pos_zero));
  assert(float_is_positive(fp64_pos_inf));
  assert(float_is_positive(fp64_pos_denormal_0));
  assert(float_is_positive(fp64_pos_normal_0));

  assert(float_is_positive(fp64_neg_snan_0) == false);
  assert(float_is_positive(fp64_neg_qnan_0) == false);
  assert(float_is_positive(fp64_neg_zero) == false);
  assert(float_is_positive(fp64_neg_inf) == false);
  assert(float_is_positive(fp64_neg_denormal_0) == false);
  assert(float_is_positive(fp64_neg_normal_0) == false);

  /* Quad floating point */
  assert(float_is_positive(fp128_pos_snan_0));
  assert(float_is_positive(fp128_pos_qnan_0));
  assert(float_is_positive(fp128_pos_zero));
  assert(float_is_positive(fp128_pos_inf));
  assert(float_is_positive(fp128_pos_denormal_0));
  assert(float_is_positive(fp128_pos_normal_0));

  assert(float_is_positive(fp128_neg_snan_0) == false);
  assert(float_is_positive(fp128_neg_qnan_0) == false);
  assert(float_is_positive(fp128_neg_zero) == false);
  assert(float_is_positive(fp128_neg_inf) == false);
  assert(float_is_positive(fp128_neg_denormal_0) == false);
  assert(float_is_positive(fp128_neg_normal_0) == false);
}

function test_float_is_negative () -> unit = {
  /* Half floating point */
  assert(float_is_negative(fp16_neg_snan_0));
  assert(float_is_negative(fp16_neg_qnan_0));
  assert(float_is_negative(fp16_neg_zero));
  assert(float_is_negative(fp16_neg_inf));
  assert(float_is_negative(fp16_neg_denormal_0));
  assert(float_is_negative(fp16_neg_normal_0));

  assert(float_is_negative(fp16_pos_snan_0) == false);
  assert(float_is_negative(fp16_pos_qnan_0) == false);
  assert(float_is_negative(fp16_pos_zero) == false);
  assert(float_is_negative(fp16_pos_inf) == false);
  assert(float_is_negative(fp16_pos_denormal_0) == false);
  assert(float_is_negative(fp16_pos_normal_0) == false);

  /* Single floating point */
  assert(float_is_negative(fp32_neg_snan_0));
  assert(float_is_negative(fp32_neg_qnan_0));
  assert(float_is_negative(fp32_neg_zero));
  assert(float_is_negative(fp32_neg_inf));
  assert(float_is_negative(fp32_neg_denormal_0));
  assert(float_is_negative(fp32_neg_normal_0));

  assert(float_is_negative(fp32_pos_snan_0) == false);
  assert(float_is_negative(fp32_pos_qnan_0) == false);
  assert(float_is_negative(fp32_pos_zero) == false);
  assert(float_is_negative(fp32_pos_inf) == false);
  assert(float_is_negative(fp32_pos_denormal_0) == false);
  assert(float_is_negative(fp32_pos_normal_0) == false);

  /* Double floating point */
  assert(float_is_negative(fp64_neg_snan_0));
  assert(float_is_negative(fp64_neg_qnan_0));
  assert(float_is_negative(fp64_neg_zero));
  assert(float_is_negative(fp64_neg_inf));
  assert(float_is_negative(fp64_neg_denormal_0));
  assert(float_is_negative(fp64_neg_normal_0));

  assert(float_is_negative(fp64_pos_snan_0) == false);
  assert(float_is_negative(fp64_pos_qnan_0) == false);
  assert(float_is_negative(fp64_pos_zero) == false);
  assert(float_is_negative(fp64_pos_inf) == false);
  assert(float_is_negative(fp64_pos_denormal_0) == false);
  assert(float_is_negative(fp64_pos_normal_0) == false);

  /* Quad floating point */
  assert(float_is_negative(fp128_neg_snan_0));
  assert(float_is_negative(fp128_neg_qnan_0));
  assert(float_is_negative(fp128_neg_zero));
  assert(float_is_negative(fp128_neg_inf));
  assert(float_is_negative(fp128_neg_denormal_0));
  assert(float_is_negative(fp128_neg_normal_0));

  assert(float_is_negative(fp128_pos_snan_0) == false);
  assert(float_is_negative(fp128_pos_qnan_0) == false);
  assert(float_is_negative(fp128_pos_zero) == false);
  assert(float_is_negative(fp128_pos_inf) == false);
  assert(float_is_negative(fp128_pos_denormal_0) == false);
  assert(float_is_negative(fp128_pos_normal_0) == false);
}

function main () -> unit = {
  test_float_is_positive();
  test_float_is_negative();
}
