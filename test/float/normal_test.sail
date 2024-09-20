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
$include <float/normal.sail>
$include "data.sail"

function test_float_is_normal () -> unit = {
  /* Half floating point */
  assert(float_is_normal(fp16_pos_normal_0));
  assert(float_is_normal(fp16_pos_normal_1));
  assert(float_is_normal(fp16_neg_normal_0));
  assert(float_is_normal(fp16_neg_normal_1));

  assert(float_is_normal(fp16_pos_inf) == false);
  assert(float_is_normal(fp16_neg_zero) == false);
  assert(float_is_normal(fp16_pos_snan_0) == false);
  assert(float_is_normal(fp16_pos_qnan_0) == false);

  /* Single floating point */
  assert(float_is_normal(fp32_pos_normal_0));
  assert(float_is_normal(fp32_pos_normal_1));
  assert(float_is_normal(fp32_neg_normal_0));
  assert(float_is_normal(fp32_neg_normal_1));

  assert(float_is_normal(fp32_pos_inf) == false);
  assert(float_is_normal(fp32_neg_zero) == false);
  assert(float_is_normal(fp32_pos_snan_0) == false);
  assert(float_is_normal(fp32_pos_qnan_0) == false);

  /* Double floating point */
  assert(float_is_normal(fp64_pos_normal_0));
  assert(float_is_normal(fp64_pos_normal_1));
  assert(float_is_normal(fp64_neg_normal_0));
  assert(float_is_normal(fp64_neg_normal_1));

  assert(float_is_normal(fp64_pos_inf) == false);
  assert(float_is_normal(fp64_neg_zero) == false);
  assert(float_is_normal(fp64_pos_snan_0) == false);
  assert(float_is_normal(fp64_pos_qnan_0) == false);

    /* Quad floating point */
  assert(float_is_normal(fp128_pos_normal_0));
  assert(float_is_normal(fp128_pos_normal_1));
  assert(float_is_normal(fp128_neg_normal_0));
  assert(float_is_normal(fp128_neg_normal_1));

  assert(float_is_normal(fp128_pos_inf) == false);
  assert(float_is_normal(fp128_neg_zero) == false);
  assert(float_is_normal(fp128_pos_snan_0) == false);
  assert(float_is_normal(fp128_pos_qnan_0) == false);
}

function test_float_is_denormal () -> unit = {
  /* Half floating point */
  assert(float_is_denormal(fp16_pos_denormal_0));
  assert(float_is_denormal(fp16_pos_denormal_1));
  assert(float_is_denormal(fp16_neg_denormal_0));
  assert(float_is_denormal(fp16_neg_denormal_1));

  assert(float_is_denormal(fp16_pos_inf) == false);
  assert(float_is_denormal(fp16_neg_zero) == false);
  assert(float_is_denormal(fp16_pos_snan_0) == false);
  assert(float_is_denormal(fp16_pos_qnan_0) == false);

  /* Single floating point */
  assert(float_is_denormal(fp32_pos_denormal_0));
  assert(float_is_denormal(fp32_pos_denormal_1));
  assert(float_is_denormal(fp32_neg_denormal_0));
  assert(float_is_denormal(fp32_neg_denormal_1));

  assert(float_is_denormal(fp32_pos_inf) == false);
  assert(float_is_denormal(fp32_neg_zero) == false);
  assert(float_is_denormal(fp32_pos_snan_0) == false);
  assert(float_is_denormal(fp32_pos_qnan_0) == false);

  /* Double floating point */
  assert(float_is_denormal(fp64_pos_denormal_0));
  assert(float_is_denormal(fp64_pos_denormal_1));
  assert(float_is_denormal(fp64_neg_denormal_0));
  assert(float_is_denormal(fp64_neg_denormal_1));

  assert(float_is_denormal(fp64_pos_inf) == false);
  assert(float_is_denormal(fp64_neg_zero) == false);
  assert(float_is_denormal(fp64_pos_snan_0) == false);
  assert(float_is_denormal(fp64_pos_qnan_0) == false);

    /* Quad floating point */
  assert(float_is_denormal(fp128_pos_denormal_0));
  assert(float_is_denormal(fp128_pos_denormal_1));
  assert(float_is_denormal(fp128_neg_denormal_0));
  assert(float_is_denormal(fp128_neg_denormal_1));

  assert(float_is_denormal(fp128_pos_inf) == false);
  assert(float_is_denormal(fp128_neg_zero) == false);
  assert(float_is_denormal(fp128_pos_snan_0) == false);
  assert(float_is_denormal(fp128_pos_qnan_0) == false);
}

function main () -> unit = {
  test_float_is_normal();
  test_float_is_denormal();
}
