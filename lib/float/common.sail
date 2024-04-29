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

$ifndef _FLOAT_COMMON
$define _FLOAT_COMMON

/* Floating point types definition */
type fp_exception_flags = bits(5) /* Floating-point exception flags. */
type fp_bits = { 'n, 'n in {16, 32, 64}. bits('n) } /* Floating-point in bits. */

/* Floating point constants */
let fp_eflag_invalid : fp_exception_flags = 0b00001

/* Floating point struct */
struct float_bits('n : Int) = {
  sign     : bits(1),
  exp      : bits(if  'n == 16
                  then 5
                  else (if   'n == 32
                        then 8
                        else 11)),
  mantissa : bits(if  'n == 16
                  then 10
                  else (if   'n == 32
                        then 23
                        else 52)),
}

/* The val func implementations */
val      float_decompose : forall 'n, 'n in { 16, 32, 64 }. bits('n) -> float_bits('n)
function float_decompose(op) = {
  match 'n {
    16 => struct {
      sign     = op[15..15],
      exp      = op[14..10],
      mantissa = op[9..0],
    },
    32 => struct {
      sign     = op[31..31],
      exp      = op[30..23],
      mantissa = op[22..0],
    },
    64 => struct {
      sign      = op[63..63],
      exp       = op[62..52],
      mantissa  = op[51..0],
    }
  }
}

$endif
