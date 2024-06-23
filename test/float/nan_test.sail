/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/* Redistribution and use in source and binary forms, with or without       */
/* modification, are permitted provided that the following conditions are   */
/* met:                                                                     */
/*                                                                          */
/* 1. Redistributions of source code must retain the above copyright        */
/*    notice, this list of conditions and the following disclaimer.         */
/* 2. Redistributions in binary form must reproduce the above copyright     */
/*    notice, this list of conditions and the following disclaimer in the   */
/*    documentation and/or other materials provided with the distribution.  */
/*                                                                          */
/* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS      */
/* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT        */
/* LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A  */
/* PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT       */
/* HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,   */
/* SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED */
/* TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR   */
/* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF   */
/* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING     */
/* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS       */
/* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.             */
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
