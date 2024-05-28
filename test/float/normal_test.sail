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
$include <float/normal.sail>

function test_float_is_normal () -> unit = {
  /* Half floating point */
  assert(float_is_normal(0x7a00));
  assert(float_is_normal(0x7801));
  assert(float_is_normal(0xf700));
  assert(float_is_normal(0xf1ff));

  assert(float_is_normal(0x7c00) == false);
  assert(float_is_normal(0x7e00) == false);
  assert(float_is_normal(0x0300) == false);
  assert(float_is_normal(0x8300) == false);

  /* Single floating point */
  assert(float_is_normal(0x7f000000));
  assert(float_is_normal(0x7f003001));
  assert(float_is_normal(0x7effffff));
  assert(float_is_normal(0xff1f0000));

  assert(float_is_normal(0x7fc00000) == false);
  assert(float_is_normal(0x7f800000) == false);
  assert(float_is_normal(0x0070f000) == false);
  assert(float_is_normal(0x8070f000) == false);

  /* Double floating point */
  assert(float_is_normal(0x7fe0000000000000));
  assert(float_is_normal(0x7fe0000000000001));
  assert(float_is_normal(0xffc000000000000f));
  assert(float_is_normal(0x8030000000100000));

  assert(float_is_normal(0x7ff8000000000000) == false);
  assert(float_is_normal(0x7ff0000000000000) == false);
  assert(float_is_normal(0x0008000000000000) == false);
  assert(float_is_normal(0x8008000000000000) == false);
}

function test_float_is_denormal () -> unit = {
  /* Half floating point */
  assert(float_is_denormal(0x0200));
  assert(float_is_denormal(0x8200));
  assert(float_is_denormal(0x02f0));
  assert(float_is_denormal(0x8201));

  assert(float_is_denormal(0x7c00) == false);
  assert(float_is_denormal(0x7e00) == false);
  assert(float_is_denormal(0x7300) == false);
  assert(float_is_denormal(0xf300) == false);

  /* Single floating point */
  assert(float_is_denormal(0x0070f000));
  assert(float_is_denormal(0x8070f000));
  assert(float_is_denormal(0x80400000));
  assert(float_is_denormal(0x00400001));

  assert(float_is_denormal(0x7fc00000) == false);
  assert(float_is_denormal(0x7f800000) == false);
  assert(float_is_denormal(0x7f000000) == false);
  assert(float_is_denormal(0xff1f0000) == false);

  /* Double floating point */
  assert(float_is_denormal(0x0008000000000000));
  assert(float_is_denormal(0x8008000000000000));
  assert(float_is_denormal(0x8000000000000001));
  assert(float_is_denormal(0x8008000000100000));

  assert(float_is_denormal(0x7ff8000000000000) == false);
  assert(float_is_denormal(0x7ff0000000000000) == false);
  assert(float_is_denormal(0xffc000000000000f) == false);
  assert(float_is_denormal(0x8030000000100000) == false);
}

function main () -> unit = {
  test_float_is_normal();
  test_float_is_denormal();
}
