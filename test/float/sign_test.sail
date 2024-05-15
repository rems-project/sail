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
$include <float/sign.sail>

function test_float_is_positive () -> unit = {
  /* Half floating point */
  assert(float_is_positive(0x7e00));
  assert(float_is_positive(0x0011));
  assert(float_is_positive(0x7fff));
  assert(float_is_positive(0x7ff1));

  assert(float_is_positive(0xc900) == false);
  assert(float_is_positive(0xdb00) == false);
  assert(float_is_positive(0x802f) == false);

  /* Single floating point */
  assert(float_is_positive(0x7fc00000));
  assert(float_is_positive(0x00003001));
  assert(float_is_positive(0x7fffffff));
  assert(float_is_positive(0x7f1f0000));

  assert(float_is_positive(0xc7800000) == false);
  assert(float_is_positive(0xdf000000) == false);
  assert(float_is_positive(0x8003f000) == false);

  /* Double floating point */
  assert(float_is_positive(0x7f080000f0f00000));
  assert(float_is_positive(0x00000fedc0000001));
  assert(float_is_positive(0x7fffffffffffffff));
  assert(float_is_positive(0x0000300000100000));

  assert(float_is_positive(0xf8f0000000023000) == false);
  assert(float_is_positive(0xfce0000000000000) == false);
  assert(float_is_positive(0xe8c0000000000000) == false);
}

function test_float_is_negative () -> unit = {
  /* Half floating point */
  assert(float_is_negative(0xfe00));
  assert(float_is_negative(0x8011));
  assert(float_is_negative(0xffff));
  assert(float_is_negative(0xfff1));

  assert(float_is_negative(0x2900) == false);
  assert(float_is_negative(0x4b00) == false);
  assert(float_is_negative(0x002f) == false);

  /* Single floating point */
  assert(float_is_negative(0xffc00000));
  assert(float_is_negative(0x80003001));
  assert(float_is_negative(0xffffffff));
  assert(float_is_negative(0xff1f0000));

  assert(float_is_negative(0x47800000) == false);
  assert(float_is_negative(0x5f000000) == false);
  assert(float_is_negative(0x0003f000) == false);

  /* Double floating point */
  assert(float_is_negative(0xff080000f0f00000));
  assert(float_is_negative(0x80000fedc0000001));
  assert(float_is_negative(0xffffffffffffffff));
  assert(float_is_negative(0x8000300000100000));

  assert(float_is_negative(0x78f0000000023000) == false);
  assert(float_is_negative(0x7ce0000000000000) == false);
  assert(float_is_negative(0x68c0000000000000) == false);
}

function main () -> unit = {
  test_float_is_positive();
  test_float_is_negative();
}
