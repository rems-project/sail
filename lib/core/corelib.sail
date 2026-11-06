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
/*  SPDX-License-Identifier: BSD-2-Clause                                   */
/*==========================================================================*/

/// When we have sizeof('n) where x : int('n), we can remove that sizeof
/// by rewriting it to __size(x).
val __id : forall 'n. int('n) -> int('n) = pure { systemverilog: "id" }

function __id(x) = x

overload __size = {__id}

val __deref : forall 'a. register('a) -> 'a = impure "reg_deref"

val lteq_int : forall 'n 'm. (int('n), int('m)) -> bool('n <= 'm) = pure { coq: "Z.leb", lean: "_lean_le", _: "lteq" }

val gteq_int : forall 'n 'm. (int('n), int('m)) -> bool('n >= 'm) = pure { coq: "Z.geb", lean: "_lean_ge", _: "gteq" }

val lt_int : forall 'n 'm. (int('n), int('m)) -> bool('n < 'm) = pure { coq: "Z.ltb", lean: "_lean_lt", _: "lt" }

val gt_int : forall 'n 'm. (int('n), int('m)) -> bool('n > 'm) = pure { coq: "Z.gtb", lean: "_lean_gt", _: "gt" }

val not_bool : forall 'p. bool('p) -> bool(not('p)) = pure { coq: "negb", lean: "_lean_not", _: "not" }

val and_bool : forall 'p 'q. (bool('p), bool('q)) -> bool('p & 'q) = pure { coq: "andb", lean: "_lean_and", _: "and_bool" }

val or_bool : forall 'p 'q. (bool('p), bool('q)) -> bool('p | 'q) = pure { coq: "orb", lean: "_lean_or", _: "or_bool" }

val add_atom : forall 'n 'm. (int('n), int('m)) -> int('n + 'm) = pure { lem: "integerAdd", coq: "Z.add", lean: "_lean_addi", _: "add_int" }

val sub_atom : forall 'n 'm. (int('n), int('m)) -> int('n - 'm) = pure { lem: "integerMinus", coq: "Z.sub", lean: "_lean_subi", _: "sub_int" }

val negate_atom : forall 'n. int('n) -> int(- 'n) = pure { ocaml: "negate", interpreter: "negate", lem: "integerNegate", coq: "Z.opp", lean: "Neg.neg", _: "neg_int" }

val mult_atom : forall 'n 'm. (int('n), int('m)) -> int('n * 'm) = pure {
  ocaml: "mult",
  interpreter: "mult",
  lem: "integerMult",
  coq: "Z.mul",
  lean: "_lean_muli",
  _: "mult_int"
}

/*! Euclidean division */
val ediv_int : forall 'n 'm. (int('n), int('m)) -> int(div('n, 'm)) = pure {
  lem: "integerDiv",
  coq: "e_div",
  lean: "Int.ediv",
  _: "ediv_int"
}

val emod_int : forall 'n 'm. (int('n), int('m)) -> int(mod('n, 'm)) = pure {
  lem: "integerMod",
  coq: "e_modulo",
  lean: "Int.emod",
  _: "emod_int"
}

val abs_int_atom : forall 'n. int('n) -> int(abs('n)) = pure {
  lem: "integerAbs",
  coq: "Z.abs",
  lean: "Int.natAbs",
  _: "abs_int"
}

$ifdef STRICT_EXPONENTIALS

val pow2 : forall 'n, 'n >= 0. int('n) -> int(2 ^ 'n) = pure { lean : "_lean_pow2i", _: "pow2" }

$else

/*!
We have special support for raising values to the power of two. Any Sail expression `2 ^ x` will be compiled to this builtin.
*/
val pow2 : forall 'n. int('n) -> int(2 ^ 'n) = pure { lean : "_lean_pow2i", _: "pow2" }

$endif

$[never_fold]
val internal_pick = impure "internal_pick" : forall ('a:Type). list('a) -> 'a

$[never_fold]
val undefined_bool = impure "undefined_bool" : unit -> bool

$[never_fold]
val undefined_bit = impure "undefined_bit" : unit -> bitvector(1)

$[never_fold]
val undefined_int = impure "undefined_int" : unit -> int

$[never_fold]
val undefined_nat = impure "undefined_nat" : unit -> nat

$[never_fold]
val undefined_real = impure "undefined_real" : unit -> real

$[never_fold]
val undefined_string = impure "undefined_string" : unit -> string

$[never_fold]
val undefined_list = impure "undefined_list" : forall 'a. 'a -> list('a)

$[never_fold]
val undefined_range = impure "undefined_range" : forall 'n 'm. (int('n), int('m)) -> range('n, 'm)

$[never_fold]
val undefined_vector = impure "undefined_vector" : forall 'n 'a. (int('n), 'a) -> vector('n, 'a)

$[never_fold]
val undefined_bitvector = impure "undefined_bitvector" : forall 'n. int('n) -> bitvector('n)

$[never_fold]
val undefined_unit = impure "undefined_unit" : unit -> unit
