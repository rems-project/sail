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
$include <float/zero.sail>
$include "data.sail"

function test_float_is_zero () -> unit = {
  /* Half floating point */
  assert(float_is_zero(fp16_pos_zero));
  assert(float_is_zero(fp16_neg_zero));

  assert(float_is_zero(fp16_pos_snan_0) == false);
  assert(float_is_zero(fp16_neg_qnan_0) == false);
  assert(float_is_zero(fp16_pos_inf) == false);
  assert(float_is_zero(fp16_pos_denormal_0) == false);
  assert(float_is_zero(fp16_neg_normal_0) == false);

  /* Single floating point */
  assert(float_is_zero(fp32_pos_zero));
  assert(float_is_zero(fp32_neg_zero));

  assert(float_is_zero(fp32_pos_snan_0) == false);
  assert(float_is_zero(fp32_neg_qnan_0) == false);
  assert(float_is_zero(fp32_pos_inf) == false);
  assert(float_is_zero(fp32_pos_denormal_0) == false);
  assert(float_is_zero(fp32_neg_normal_0) == false);

  /* Double floating point */
  assert(float_is_zero(fp64_pos_zero));
  assert(float_is_zero(fp64_neg_zero));

  assert(float_is_zero(fp64_pos_snan_0) == false);
  assert(float_is_zero(fp64_neg_qnan_0) == false);
  assert(float_is_zero(fp64_pos_inf) == false);
  assert(float_is_zero(fp64_pos_denormal_0) == false);
  assert(float_is_zero(fp64_neg_normal_0) == false);

  /* Quad floating point */
  assert(float_is_zero(fp128_pos_zero));
  assert(float_is_zero(fp128_neg_zero));

  assert(float_is_zero(fp128_pos_snan_0) == false);
  assert(float_is_zero(fp128_neg_qnan_0) == false);
  assert(float_is_zero(fp128_pos_inf) == false);
  assert(float_is_zero(fp128_pos_denormal_0) == false);
  assert(float_is_zero(fp128_neg_normal_0) == false);
}

function main () -> unit = {
  test_float_is_zero();
}
