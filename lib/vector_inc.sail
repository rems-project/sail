/*==========================================================================*/
/*     Sail                                                                 */
/*                                                                          */
/*  Sail and the Sail architecture models here, comprising all files and    */
/*  directories except the ASL-derived Sail code in the aarch64 directory,  */
/*  are subject to the BSD two-clause licence below.                        */
/*                                                                          */
/*  The ASL derived parts of the ARMv8.3 specification in                   */
/*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               */
/*                                                                          */
/*  Copyright (c) 2013-2021                                                 */
/*    Kathyrn Gray                                                          */
/*    Shaked Flur                                                           */
/*    Stephen Kell                                                          */
/*    Gabriel Kerneis                                                       */
/*    Robert Norton-Wright                                                  */
/*    Christopher Pulte                                                     */
/*    Peter Sewell                                                          */
/*    Alasdair Armstrong                                                    */
/*    Brian Campbell                                                        */
/*    Thomas Bauereiss                                                      */
/*    Anthony Fox                                                           */
/*    Jon French                                                            */
/*    Dominic Mulligan                                                      */
/*    Stephen Kell                                                          */
/*    Mark Wassell                                                          */
/*    Alastair Reid (Arm Ltd)                                               */
/*                                                                          */
/*  All rights reserved.                                                    */
/*                                                                          */
/*  This work was partially supported by EPSRC grant EP/K008528/1 <a        */
/*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          */
/*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   */
/*  KTF funding, and donations from Arm.  This project has received         */
/*  funding from the European Research Council (ERC) under the European     */
/*  Union’s Horizon 2020 research and innovation programme (grant           */
/*  agreement No 789108, ELVER).                                            */
/*                                                                          */
/*  This software was developed by SRI International and the University of  */
/*  Cambridge Computer Laboratory (Department of Computer Science and       */
/*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        */
/*  and FA8750-10-C-0237 ("CTSRD").                                         */
/*                                                                          */
/*  Redistribution and use in source and binary forms, with or without      */
/*  modification, are permitted provided that the following conditions      */
/*  are met:                                                                */
/*  1. Redistributions of source code must retain the above copyright       */
/*     notice, this list of conditions and the following disclaimer.        */
/*  2. Redistributions in binary form must reproduce the above copyright    */
/*     notice, this list of conditions and the following disclaimer in      */
/*     the documentation and/or other materials provided with the           */
/*     distribution.                                                        */
/*                                                                          */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      */
/*  SUCH DAMAGE.                                                            */
/*==========================================================================*/

$ifndef _VECTOR_INC
$define _VECTOR_INC

$include <flow.sail>

type bits ('n : Int) = bitvector('n, inc)

val eq_bit = pure "eq_bit" : (bit, bit) -> bool

val eq_bits = pure {
  ocaml: "eq_list",
  interpreter: "eq_list",
  lem: "eq_vec",
  c: "eq_bits",
  coq: "eq_vec"
} : forall 'n. (bits('n), bits('n)) -> bool

val not_vec = pure {c: "not_bits", _: "not_vec"} : forall 'n. bits('n) -> bits('n)

overload operator == = {eq_bit, eq_bits}

val bitvector_length = pure {coq: "length_mword", _:"length"} : forall 'n. bits('n) -> atom('n)

val vector_length = pure {
  ocaml: "length",
  interpreter: "length",
  lem: "length_list",
  c: "length",
  coq: "length_list"
} : forall 'n ('a : Type). vector('n, inc, 'a) -> atom('n)

overload length = {bitvector_length, vector_length}

val sail_zeros = pure "zeros" : forall 'n. int('n) -> bits('n)

val sail_ones : forall 'n, 'n >= 0. int('n) -> bits('n)

function sail_ones(n) = not_vec(sail_zeros(n))

val print_bits = pure "print_bits" : forall 'n. (string, bits('n)) -> unit

val sail_sign_extend = pure "sign_extend" : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

val sail_zero_extend = pure "zero_extend" : forall 'n 'm, 'm >= 'n. (bits('n), int('m)) -> bits('m)

val truncate = pure {
  ocaml: "vector_truncate",
  interpreter: "vector_truncate",
  lem: "vector_truncate",
  coq: "vector_truncate",
  c: "truncate"
} : forall 'm 'n, 'm >= 0 & 'm <= 'n. (bits('n), atom('m)) -> bits('m)

val mask : forall 'len 'v, 'len >= 0 & 'v >= 0. (atom('len), bits('v)) -> bits('len)

function mask(len, v) = if len <= length(v) then truncate(v, len) else sail_zero_extend(v, len)

overload operator ^ = {mask}

val bitvector_concat = pure {ocaml: "append", interpreter: "append", lem: "concat_vec", c: "append", coq: "concat_vec"} : forall ('n : Int) ('m : Int).
  (bits('n), bits('m)) -> bits('n + 'm)

overload append = {bitvector_concat}

/* Used for creating long bitvector literals in the C backend. */
val "append_64" : forall 'n. (bits('n), bits(64)) -> bits('n + 64)

val bitvector_access = pure {
  ocaml: "access",
  interpreter: "access",
  lem: "access_vec_inc",
  coq: "access_vec_inc",
  c: "vector_access"
} : forall ('n : Int) ('m : Int), 0 <= 'm < 'n . (bits('n), int('m)) -> bit

val plain_vector_access = pure {
  ocaml: "access",
  interpreter: "access",
  lem: "access_list_inc",
  coq: "access_list_inc",
  c: "vector_access"
} : forall ('n : Int) ('m : Int) ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), atom('m)) -> 'a

overload vector_access = {bitvector_access, plain_vector_access}

val bitvector_update = pure {
  ocaml: "update",
  interpreter: "update",
  lem: "update_vec_inc",
  coq: "update_vec_inc",
  c: "vector_update"
} : forall 'n 'm, 0 <= 'm < 'n. (bits('n), atom('m), bit) -> bits('n)

val plain_vector_update = pure {
  ocaml: "update",
  interpreter: "update",
  lem: "update_list_inc",
  coq: "update_list_inc",
  c: "vector_update"
} : forall 'n 'm ('a : Type), 0 <= 'm < 'n. (vector('n, inc, 'a), atom('m), 'a) -> vector('n, inc, 'a)

overload vector_update = {bitvector_update, plain_vector_update}

val add_bits = pure {
  ocaml: "add_vec",
  interpreter: "add_vec",
  c: "add_bits"
} : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_bits_int = pure {
  ocaml: "add_vec_int", interpreter: "add_vec_int",
  c: "add_bits_int"
} : forall 'n. (bits('n), int) -> bits('n)

overload operator + = {add_bits, add_bits_int}

val subrange_bits = pure {
  ocaml: "subrange",
  interpreter: "subrange",
  lem: "subrange_vec_inc",
  c: "vector_subrange",
  coq: "subrange_vec_inc"
} : forall ('n : Int) ('m : Int) ('o : Int), 0 <= 'm <= 'o < 'n.
  (bits('n), atom('m), atom('o)) -> bits('o - 'm + 1)

overload vector_subrange = {subrange_bits}

val update_subrange_bits = pure {
  ocaml: "update_subrange",
  interpreter: "update_subrange",
  lem: "update_subrange_vec_inc",
  c: "vector_update_subrange",
  coq: "update_subrange_vec_inc"
} : forall 'n 'm 'o, 0 <= 'm <= 'o < 'n. (bits('n), atom('m), atom('o), bits('m - ('o - 1))) -> bits('n)

overload vector_update_subrange = {update_subrange_bits}

// Some ARM specific builtins

/*
val get_slice_int = pure "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val set_slice_int = pure "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val set_slice_bits = pure "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)
*/

val replicate_bits = pure "replicate_bits" : forall 'n 'm. (bits('n), atom('m)) -> bits('n * 'm)

val unsigned = pure {
  ocaml: "uint",
  lem: "uint",
  interpreter: "uint",
  c: "sail_uint",
  coq: "uint"
} : forall 'n. bits('n) -> range(0, 2 ^ 'n - 1)

/* We need a non-empty vector so that the range makes sense */
val signed = pure "sint" : forall 'n, 'n > 0. bits('n) -> range(- (2 ^ ('n - 1)), 2 ^ ('n - 1) - 1)

$endif
