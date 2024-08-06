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
$include <float/le.sail>
$include "tuple_equality.sail"
$include "data.sail"

function test_float_is_le () -> unit = {
  /* Half floating point */
  assert(float_is_le((fp16_pos_snan_0, fp16_neg_snan_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp16_pos_qnan_0, fp16_pos_normal_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp16_neg_denormal_0, fp16_neg_snan_0)) == (false, fp_eflag_invalid));

  assert(float_is_le((fp16_neg_zero, fp16_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_pos_zero, fp16_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_zero, fp16_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_pos_zero, fp16_neg_zero)) == (true, fp_eflag_none));

  assert(float_is_le((fp16_pos_inf, fp16_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_inf, fp16_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_inf, fp16_neg_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_inf, fp16_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_inf, fp16_pos_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_inf, fp16_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_pos_inf, fp16_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_pos_inf, fp16_neg_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp16_pos_inf, fp16_neg_zero)) == (false, fp_eflag_none));
  assert(float_is_le((fp16_pos_inf, fp16_pos_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp16_pos_inf, fp16_pos_normal_0)) == (false, fp_eflag_none));

  assert(float_is_le((fp16_pos_normal_0, fp16_pos_normal_1)) == (false, fp_eflag_none));
  assert(float_is_le((fp16_pos_normal_1, fp16_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_pos_normal_0, fp16_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_normal_0, fp16_neg_normal_1)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_normal_1, fp16_neg_normal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp16_neg_normal_0, fp16_neg_normal_0)) == (true, fp_eflag_none));

  assert(float_is_le((fp16_pos_denormal_0, fp16_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp16_neg_denormal_0, fp16_neg_normal_0)) == (false, fp_eflag_none));

  /* Single floating point */
  assert(float_is_le((fp32_pos_snan_0, fp32_neg_snan_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp32_pos_qnan_0, fp32_pos_normal_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp32_neg_denormal_0, fp32_neg_snan_0)) == (false, fp_eflag_invalid));

  assert(float_is_le((fp32_neg_zero, fp32_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_pos_zero, fp32_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_zero, fp32_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_pos_zero, fp32_neg_zero)) == (true, fp_eflag_none));

  assert(float_is_le((fp32_pos_inf, fp32_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_inf, fp32_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_inf, fp32_neg_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_inf, fp32_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_inf, fp32_pos_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_inf, fp32_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_pos_inf, fp32_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_pos_inf, fp32_neg_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp32_pos_inf, fp32_neg_zero)) == (false, fp_eflag_none));
  assert(float_is_le((fp32_pos_inf, fp32_pos_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp32_pos_inf, fp32_pos_normal_0)) == (false, fp_eflag_none));

  assert(float_is_le((fp32_pos_normal_0, fp32_pos_normal_1)) == (false, fp_eflag_none));
  assert(float_is_le((fp32_pos_normal_1, fp32_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_pos_normal_0, fp32_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_normal_0, fp32_neg_normal_1)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_normal_1, fp32_neg_normal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp32_neg_normal_0, fp32_neg_normal_0)) == (true, fp_eflag_none));

  assert(float_is_le((fp32_pos_denormal_0, fp32_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp32_neg_denormal_0, fp32_neg_normal_0)) == (false, fp_eflag_none));

  /* Double floating point */
  assert(float_is_le((fp64_pos_snan_0, fp64_neg_snan_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp64_pos_qnan_0, fp64_pos_normal_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp64_neg_denormal_0, fp64_neg_snan_0)) == (false, fp_eflag_invalid));

  assert(float_is_le((fp64_neg_zero, fp64_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_pos_zero, fp64_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_zero, fp64_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_pos_zero, fp64_neg_zero)) == (true, fp_eflag_none));

  assert(float_is_le((fp64_pos_inf, fp64_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_inf, fp64_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_inf, fp64_neg_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_inf, fp64_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_inf, fp64_pos_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_inf, fp64_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_pos_inf, fp64_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_pos_inf, fp64_neg_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp64_pos_inf, fp64_neg_zero)) == (false, fp_eflag_none));
  assert(float_is_le((fp64_pos_inf, fp64_pos_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp64_pos_inf, fp64_pos_normal_0)) == (false, fp_eflag_none));

  assert(float_is_le((fp64_pos_normal_0, fp64_pos_normal_1)) == (false, fp_eflag_none));
  assert(float_is_le((fp64_pos_normal_1, fp64_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_pos_normal_0, fp64_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_normal_0, fp64_neg_normal_1)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_normal_1, fp64_neg_normal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp64_neg_normal_0, fp64_neg_normal_0)) == (true, fp_eflag_none));

  assert(float_is_le((fp64_pos_denormal_0, fp64_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp64_neg_denormal_0, fp64_neg_normal_0)) == (false, fp_eflag_none));

  /* Quad floating point */
  assert(float_is_le((fp128_pos_snan_0, fp128_neg_snan_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp128_pos_qnan_0, fp128_pos_normal_0)) == (false, fp_eflag_invalid));
  assert(float_is_le((fp128_neg_denormal_0, fp128_neg_snan_0)) == (false, fp_eflag_invalid));

  assert(float_is_le((fp128_neg_zero, fp128_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_pos_zero, fp128_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_zero, fp128_pos_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_pos_zero, fp128_neg_zero)) == (true, fp_eflag_none));

  assert(float_is_le((fp128_pos_inf, fp128_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_inf, fp128_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_inf, fp128_neg_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_inf, fp128_neg_zero)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_inf, fp128_pos_denormal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_inf, fp128_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_pos_inf, fp128_pos_inf)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_pos_inf, fp128_neg_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp128_pos_inf, fp128_neg_zero)) == (false, fp_eflag_none));
  assert(float_is_le((fp128_pos_inf, fp128_pos_denormal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp128_pos_inf, fp128_pos_normal_0)) == (false, fp_eflag_none));

  assert(float_is_le((fp128_pos_normal_0, fp128_pos_normal_1)) == (false, fp_eflag_none));
  assert(float_is_le((fp128_pos_normal_1, fp128_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_pos_normal_0, fp128_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_normal_0, fp128_neg_normal_1)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_normal_1, fp128_neg_normal_0)) == (false, fp_eflag_none));
  assert(float_is_le((fp128_neg_normal_0, fp128_neg_normal_0)) == (true, fp_eflag_none));

  assert(float_is_le((fp128_pos_denormal_0, fp128_pos_normal_0)) == (true, fp_eflag_none));
  assert(float_is_le((fp128_neg_denormal_0, fp128_neg_normal_0)) == (false, fp_eflag_none));
}

function main () -> unit = {
  test_float_is_le();
}
