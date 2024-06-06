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
$include <float/eq.sail>
$include "tuple_equality.sail"

function test_float_is_eq () -> unit = {
  /* Half floating point */
  assert(float_is_eq((0x0001, 0x0001)) == (true, fp_eflag_none));
  assert(float_is_eq((0x0700, 0x0700)) == (true, fp_eflag_none));
  assert(float_is_eq((0x0000, 0x8000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x7c00, 0x7c00)) == (true, fp_eflag_none));

  assert(float_is_eq((0x0001, 0x8001)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7c00, 0xfc00)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7e01, 0x7a01)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7ef1, 0x7ef1)) == (false, fp_eflag_none));

  assert(float_is_eq((0x7c01, 0x7e0f)) == (false, fp_eflag_invalid));
  assert(float_is_eq((0xf021, 0x7c0f)) == (false, fp_eflag_invalid));

  /* Single floating point */
  assert(float_is_eq((0x00001000, 0x00001000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x80301000, 0x80301000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x00000000, 0x80000000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x7f800000, 0x7f800000)) == (true, fp_eflag_none));

  assert(float_is_eq((0x00001000, 0x80001000)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7fc00000, 0x80301000)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7fc00001, 0x01234000)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7f800000, 0xff800000)) == (false, fp_eflag_none));

  assert(float_is_eq((0x7f800001, 0x01234000)) == (false, fp_eflag_invalid));
  assert(float_is_eq((0x7c800000, 0xff80000f)) == (false, fp_eflag_invalid));

  /* Double floating point */
  assert(float_is_eq((0x0000000000000001, 0x0000000000000001)) == (true, fp_eflag_none));
  assert(float_is_eq((0x0f0000000000000f, 0x0f0000000000000f)) == (true, fp_eflag_none));
  assert(float_is_eq((0x8000000000000000, 0x0000000000000000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x7ff0000000000000, 0x7ff0000000000000)) == (true, fp_eflag_none));

  assert(float_is_eq((0x0000000000000001, 0x8000000000000001)) == (false, fp_eflag_none));
  assert(float_is_eq((0x0f0000000000000f, 0x3f0000000000000f)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7ff8000000000000, 0x0000234db0000000)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7ff8000000000000, 0xfff8000000000000)) == (false, fp_eflag_none));

  assert(float_is_eq((0x7ff7000000000000, 0x0000234db0000000)) == (false, fp_eflag_invalid));
  assert(float_is_eq((0x7ff0000000000001, 0xfff0000003000001)) == (false, fp_eflag_invalid));

  /* Quad floating point */
  assert(float_is_eq((0x00000000000000000000000000000001, 0x00000000000000000000000000000001)) == (true, fp_eflag_none));
  assert(float_is_eq((0x0f00000000000000000000000000000f, 0x0f00000000000000000000000000000f)) == (true, fp_eflag_none));
  assert(float_is_eq((0x80000000000000000000000000000000, 0x00000000000000000000000000000000)) == (true, fp_eflag_none));
  assert(float_is_eq((0x7fff0000000000000000000000000000, 0x7fff0000000000000000000000000000)) == (true, fp_eflag_none));

  assert(float_is_eq((0x00000000000000000000000000000001, 0x80000000000000000000000000000001)) == (false, fp_eflag_none));
  assert(float_is_eq((0x0f00000000000000000000000000000f, 0x3f00000000000000000000000000000f)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7fff8000000000000000000000000000, 0x0000234db00000000000000000000000)) == (false, fp_eflag_none));
  assert(float_is_eq((0x7fff8000000000000000000000000000, 0xffff8000000000000000000000000000)) == (false, fp_eflag_none));

  assert(float_is_eq((0x7fff7000000000000000000000000000, 0x0000234db00000000000000000000000)) == (false, fp_eflag_invalid));
  assert(float_is_eq((0x7fff0000000000000000000000000001, 0xfff00000030000000000000000000001)) == (false, fp_eflag_invalid));
}

function main () -> unit = {
  test_float_is_eq();
}
