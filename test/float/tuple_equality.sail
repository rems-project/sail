/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/* Copyright 2024 Intel Corporation                                         */
/*   Pan Li - pan2.li@intel.com                                             */
/*                                                                          */
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

$ifndef _FLOAT_TUPLE_EQUALITY
$define _FLOAT_TUPLE_EQUALITY

$include <float/common.sail>

/* Floating point related tuple implementations for test */
val      bool_and_flags_eq : (fp_bool_and_flags, fp_bool_and_flags) -> bool
function bool_and_flags_eq ((bool_0, flags_0), (bool_1, flags_1)) = {
  let is_eq = (bool_0 == bool_1) & (flags_0 == flags_1);

  is_eq;
}

overload operator == = {bool_and_flags_eq}

$endif
