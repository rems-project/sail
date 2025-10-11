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
$include <float/common.sail>
$include <float/rounding.sail>

function test_float_rounding () -> unit = {
  float_set_rounding (fp_rounding_rne);
  assert(fp_rounding_rne == float_get_rounding ());

  float_set_rounding (fp_rounding_rna);
  assert(fp_rounding_rna == float_get_rounding ());

  float_set_rounding (fp_rounding_rdn);
  assert(fp_rounding_rdn == float_get_rounding ());

  float_set_rounding (fp_rounding_rup);
  assert(fp_rounding_rup == float_get_rounding ());

  float_set_rounding (fp_rounding_rtz);
  assert(fp_rounding_rtz == float_get_rounding ());
}

function main () -> unit = {
  test_float_rounding ();
}
