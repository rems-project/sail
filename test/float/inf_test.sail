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
$include <float/inf.sail>

function test_float_is_inf () -> unit = {
  /* Half floating point */
  assert(float_is_inf(0x7c00));
  assert(float_is_inf(0xfc00));

  assert(float_is_inf(0x7a00) == false);
  assert(float_is_inf(0x7b00) == false);
  assert(float_is_inf(0x7e00) == false);
  assert(float_is_inf(0xca00) == false);
  assert(float_is_inf(0xdb00) == false);
  assert(float_is_inf(0xfe00) == false);

  /* Single floating point */
  assert(float_is_inf(0x7f800000));
  assert(float_is_inf(0xff800000));

  assert(float_is_inf(0x7fc00000) == false);
  assert(float_is_inf(0x7f000001) == false);
  assert(float_is_inf(0x7e800000) == false);
  assert(float_is_inf(0xffc00000) == false);
  assert(float_is_inf(0xff000001) == false);
  assert(float_is_inf(0xfe800000) == false);

  /* Double floating point */
  assert(float_is_inf(0x7ff0000000000000));
  assert(float_is_inf(0xfff0000000000000));

  assert(float_is_inf(0x7ff8000000000000) == false);
  assert(float_is_inf(0x7ff0000000000001) == false);
  assert(float_is_inf(0x7fc0000000000000) == false);
  assert(float_is_inf(0xfff8000000000000) == false);
  assert(float_is_inf(0xfff0000000000001) == false);
  assert(float_is_inf(0xffc0000000000000) == false);

    /* Quad floating point */
  assert(float_is_inf(0x7fff0000000000000000000000000000));
  assert(float_is_inf(0xffff0000000000000000000000000000));

  assert(float_is_inf(0x7fff8000000000000000000000000000) == false);
  assert(float_is_inf(0x7fff0000000000000000000000000001) == false);
  assert(float_is_inf(0x7ffc0000000000000000000000000000) == false);
  assert(float_is_inf(0xffff8000000000000000000000000000) == false);
  assert(float_is_inf(0xffff0000000000000000000000000001) == false);
  assert(float_is_inf(0xfffc0000000000000000000000000000) == false);
}

function main () -> unit = {
  test_float_is_inf();
}
