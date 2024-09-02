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

$endif
