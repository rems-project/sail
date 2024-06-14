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
$include <float/ne.sail>
$include "tuple_equality.sail"

function test_float_is_ne () -> unit = {
  /* Half floating point */
  assert(float_is_ne((0x0001, 0x0011)) == (true, fp_eflag_none));
  assert(float_is_ne((0x0701, 0x0700)) == (true, fp_eflag_none));
  assert(float_is_ne((0x0000, 0x0001)) == (true, fp_eflag_none));
  assert(float_is_ne((0x7c00, 0xfc00)) == (true, fp_eflag_none));

  assert(float_is_ne((0x0001, 0x0001)) == (false, fp_eflag_none));
  assert(float_is_ne((0x7c00, 0x7c00)) == (false, fp_eflag_none));
  assert(float_is_ne((0x0000, 0x8000)) == (false, fp_eflag_none));
  assert(float_is_ne((0x7ef1, 0x7ef1)) == (false, fp_eflag_none));

  assert(float_is_ne((0x7c01, 0x7e0f)) == (false, fp_eflag_invalid));
  assert(float_is_ne((0xf021, 0x7c0f)) == (false, fp_eflag_invalid));

  /* Single floating point */
  assert(float_is_ne((0x00001000, 0x80001000)) == (true, fp_eflag_none));
  assert(float_is_ne((0x80300000, 0x80301000)) == (true, fp_eflag_none));
  assert(float_is_ne((0x00000001, 0x80000000)) == (true, fp_eflag_none));
  assert(float_is_ne((0x7f800000, 0xff800000)) == (true, fp_eflag_none));

  assert(float_is_ne((0x00001000, 0x00001000)) == (false, fp_eflag_none));
  assert(float_is_ne((0x80301000, 0x80301000)) == (false, fp_eflag_none));
  assert(float_is_ne((0x00000000, 0x80000000)) == (false, fp_eflag_none));
  assert(float_is_ne((0x7fc00000, 0x7fc00000)) == (false, fp_eflag_none));

  assert(float_is_ne((0x7f800001, 0x01234000)) == (false, fp_eflag_invalid));
  assert(float_is_ne((0x7c800000, 0xff80000f)) == (false, fp_eflag_invalid));

  /* Double floating point */
  assert(float_is_ne((0x8000000000000001, 0x0000000000000001)) == (true, fp_eflag_none));
  assert(float_is_ne((0x8f0000000000000f, 0x0f0000000000000f)) == (true, fp_eflag_none));
  assert(float_is_ne((0x8000000000000000, 0x0000000000000001)) == (true, fp_eflag_none));
  assert(float_is_ne((0x7ff0000000000000, 0xfff0000000000000)) == (true, fp_eflag_none));

  assert(float_is_ne((0x0000000000000011, 0x0000000000000011)) == (false, fp_eflag_none));
  assert(float_is_ne((0x0fff00000000000f, 0x0fff00000000000f)) == (false, fp_eflag_none));
  assert(float_is_ne((0x0000000000000000, 0x8000000000000000)) == (false, fp_eflag_none));
  assert(float_is_ne((0x7ff8000000000100, 0x7ff8000000000100)) == (false, fp_eflag_none));

  assert(float_is_ne((0x7ff7000000000000, 0x0000234db0000000)) == (false, fp_eflag_invalid));
  assert(float_is_ne((0x7ff0000000000001, 0xfff0000003000001)) == (false, fp_eflag_invalid));
}

function main () -> unit = {
  test_float_is_ne();
}
