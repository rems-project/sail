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
$include <float/nan.sail>

function test_float_is_nan () -> unit = {
  /* Half floating point */
  assert(float_is_nan(0x7e00));
  assert(float_is_nan(0x7c01));
  assert(float_is_nan(0x7c10));
  assert(float_is_nan(0x7f01));

  assert(float_is_nan(0xfe00));
  assert(float_is_nan(0xfc01));
  assert(float_is_nan(0xfc10));
  assert(float_is_nan(0xff01));

  assert(float_is_nan(0x7a00) == false);
  assert(float_is_nan(0x7b00) == false);
  assert(float_is_nan(0x7c00) == false);
  assert(float_is_nan(0xca00) == false);
  assert(float_is_nan(0xdb00) == false);
  assert(float_is_nan(0xfc00) == false);

  /* Single floating point */
  assert(float_is_nan(0x7fc00000));
  assert(float_is_nan(0x7f800001));
  assert(float_is_nan(0x7fc00100));
  assert(float_is_nan(0x7ff10000));

  assert(float_is_nan(0xffc00000));
  assert(float_is_nan(0xff800001));
  assert(float_is_nan(0xffc00100));
  assert(float_is_nan(0xfff10000));

  assert(float_is_nan(0x7f800000) == false);
  assert(float_is_nan(0x7f000000) == false);
  assert(float_is_nan(0x7e800000) == false);
  assert(float_is_nan(0xcf800000) == false);
  assert(float_is_nan(0xdf000000) == false);
  assert(float_is_nan(0xfe800000) == false);

  /* Double floating point */
  assert(float_is_nan(0x7ff8000000000000));
  assert(float_is_nan(0x7ff0000000000001));
  assert(float_is_nan(0x7ff8000000000100));
  assert(float_is_nan(0x7ffc000000100000));

  assert(float_is_nan(0xfff8000000000000));
  assert(float_is_nan(0xfff0000000000001));
  assert(float_is_nan(0xfff8000000000100));
  assert(float_is_nan(0xfffc000000100000));

  assert(float_is_nan(0x7ff0000000000000) == false);
  assert(float_is_nan(0x7fe0000000000000) == false);
  assert(float_is_nan(0x7fc0000000000000) == false);
  assert(float_is_nan(0xfff0000000000000) == false);
  assert(float_is_nan(0xffe0000000000000) == false);
  assert(float_is_nan(0xffc0000000000000) == false);

  /* Quad floating point */
  assert(float_is_nan(0x7fff8000000000000000000000000000));
  assert(float_is_nan(0x7fff0000000000000000000000000001));
  assert(float_is_nan(0x7fff8000000000000000000000000100));
  assert(float_is_nan(0x7fffc000000000001000000000000000));

  assert(float_is_nan(0xffff8000000000000000000000000000));
  assert(float_is_nan(0xffff0000000000000000000000000001));
  assert(float_is_nan(0xffff8000000000000000000000000100));
  assert(float_is_nan(0xffffc000000000001000000000000000));

  assert(float_is_nan(0x7fff0000000000000000000000000000) == false);
  assert(float_is_nan(0x7ffe0000000000000000000000000000) == false);
  assert(float_is_nan(0x7ffc0000000000000000000000000000) == false);
  assert(float_is_nan(0xffff0000000000000000000000000000) == false);
  assert(float_is_nan(0xfffe0000000000000000000000000000) == false);
  assert(float_is_nan(0xfffc0000000000000000000000000000) == false);
}

function test_float_is_snan () -> unit = {
  /* Half floating point */
  assert(float_is_snan(0x7d00));
  assert(float_is_snan(0x7d01));

  assert(float_is_snan(0xfd00));
  assert(float_is_snan(0xfd01));

  assert(float_is_snan(0x7e00) == false);
  assert(float_is_snan(0xde01) == false);
  assert(float_is_snan(0xff01) == false);

  /* Single floating point */
  assert(float_is_snan(0x7fa00000));
  assert(float_is_snan(0x7fa00001));

  assert(float_is_snan(0xffa00000));
  assert(float_is_snan(0xffa00001));

  assert(float_is_snan(0x7fc00000) == false);
  assert(float_is_snan(0xffc00001) == false);
  assert(float_is_snan(0xfec00001) == false);

  /* Double floating point */
  assert(float_is_snan(0x7ff7000000000000));
  assert(float_is_snan(0x7ff7000000000001));

  assert(float_is_snan(0xfff7000000000000));
  assert(float_is_snan(0xfff7000000000001));

  assert(float_is_snan(0x7ff8000000000000) == false);
  assert(float_is_snan(0xfff8000000000000) == false);
  assert(float_is_snan(0xfef8000000000001) == false);

  /* Quad floating point */
  assert(float_is_snan(0x7fff7000000000000000000000000000));
  assert(float_is_snan(0x7fff7000000000000000000000000001));

  assert(float_is_snan(0xffff7000000000000000000000000000));
  assert(float_is_snan(0xffff7000000000000000000000000001));

  assert(float_is_snan(0x7fff8000000000000000000000000000) == false);
  assert(float_is_snan(0xffff8000000000000000000000000000) == false);
  assert(float_is_snan(0xfeff8000000000000000000000000001) == false);

}

function test_float_is_qnan () -> unit = {
  /* Half floating point */
  assert(float_is_qnan(0x7e00));
  assert(float_is_qnan(0x7e01));

  assert(float_is_qnan(0xfe00));
  assert(float_is_qnan(0xfe01));

  assert(float_is_qnan(0x7c00) == false);
  assert(float_is_qnan(0xdc01) == false);
  assert(float_is_qnan(0xfc01) == false);

  /* Single floating pont */
  assert(float_is_qnan(0x7fc00000));
  assert(float_is_qnan(0x7fc00001));

  assert(float_is_qnan(0xffc00000));
  assert(float_is_qnan(0xffc00001));

  assert(float_is_qnan(0x7fa00000) == false);
  assert(float_is_qnan(0xffa00001) == false);
  assert(float_is_qnan(0xfea00001) == false);

  /* Double floating point */
  assert(float_is_qnan(0x7ff8000000000000));
  assert(float_is_qnan(0x7ff8000000000001));

  assert(float_is_qnan(0xfff8000000000000));
  assert(float_is_qnan(0xfff8000000000001));

  assert(float_is_qnan(0x7ff7000000000000) == false);
  assert(float_is_qnan(0xfff7000000000000) == false);
  assert(float_is_qnan(0xfef7000000000001) == false);

  /* Quad floating point */
  assert(float_is_qnan(0x7fff8000000000000000000000000000));
  assert(float_is_qnan(0x7fff8000000000000000000000000001));

  assert(float_is_qnan(0xffff8000000000000000000000000000));
  assert(float_is_qnan(0xffff8000000000000000000000000001));

  assert(float_is_qnan(0x7fff7000000000000000000000000000) == false);
  assert(float_is_qnan(0xffff7000000000000000000000000000) == false);
  assert(float_is_qnan(0xfeff7000000000000000000000000001) == false);
}

function main () -> unit = {
  test_float_is_nan();
  test_float_is_snan();
  test_float_is_qnan();
}
