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
type fp_bits = { 'n, 'n in {16, 32, 64, 128}. bits('n) } /* Floating-point in bits. */
type fp_bits_x2 = { 'n, 'n in {16, 32, 64, 128}. (bits('n), bits('n)) } /* Floating point x2 tuple */
type fp_bool_and_flags = (bool, fp_exception_flags) /* Floating point bool and exception flags tuple */

/* Floating point constants */
let fp_eflag_none    : fp_exception_flags = 0b00000
let fp_eflag_invalid : fp_exception_flags = 0b00001

/* Floating point struct */
struct float_bits('n : Int) = {
  sign     : bits(1),
  exp      : bits(if  'n == 16
                  then 5
                  else (if   'n == 32
                        then 8
                        else (if   'n == 64
                              then 11
                              else 15))),
  mantissa : bits(if  'n == 16
                  then 10
                  else (if   'n == 32
                        then 23
                        else (if   'n == 64
                              then 52
                              else 112))),
}

/* The val func implementations */
val      float_decompose : forall 'n, 'n in { 16, 32, 64, 128 }. bits('n) -> float_bits('n)
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
    },
    128 => struct {
      sign      = op[127..127],
      exp       = op[126..112],
      mantissa  = op[111..0],
    }
  }
}

val      not : forall ('p : Bool). bool('p) -> bool(not('p))
function not(b) = not_bool(b)

val      is_lowest_one : forall 'n, 0 < 'n. bits('n) -> bool
function is_lowest_one (op) = op[0] == bitone

val      is_highest_one : forall 'n, 0 < 'n. bits('n) -> bool
function is_highest_one (op) = op['n - 1] == bitone

val      is_all_ones : forall 'n, 0 < 'n. bits('n) -> bool
function is_all_ones (op) = op == sail_ones ('n)

val      is_lowest_zero : forall 'n, 0 < 'n. bits('n) -> bool
function is_lowest_zero (op) = op[0] == bitzero

val      is_highest_zero : forall 'n, 0 < 'n. bits('n) -> bool
function is_highest_zero (op) = op['n - 1] == bitzero

val      is_all_zeros : forall 'n, 0 < 'n. bits('n) -> bool
function is_all_zeros (op) = op == sail_zeros ('n)

$endif
