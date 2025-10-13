/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_NORMAL
$define _FLOAT_NORMAL

$include <float/common.sail>

val      float_is_normal : fp_bits -> bool
function float_is_normal (op) = {
  let struct {_, exp} = float_decompose(op);
  let is_normal       = not_bool (is_all_ones (exp)) & not_bool (is_all_zeros (exp));

  is_normal
}

val      float_is_subnormal : fp_bits -> bool
function float_is_subnormal (op) = {
  let struct {_, exp, mantissa} = float_decompose(op);
  let is_subnormal               = is_all_zeros (exp) & not_bool (is_all_zeros (mantissa));

  is_subnormal
}

$endif
