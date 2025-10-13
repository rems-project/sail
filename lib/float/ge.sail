/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_GE
$define _FLOAT_GE

$include <float/common.sail>
$include <float/nan.sail>
$include <float/arith_internal.sail>

val      float_is_ge : forall 'n, is_fp_bits('n) . (bits('n), bits('n)) -> (bool, fp_exception_flags)
function float_is_ge (op_0, op_1) = {
  let is_nan  = float_is_nan (op_0) | float_is_nan (op_1);
  let flags   = if   is_nan
                then fp_eflag_invalid
                else fp_eflag_none;
  let is_ge   = not_bool (is_nan) & float_is_ge_internal (op_0, op_1);

  (is_ge, flags);
}

$endif
