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

$ifndef _FLOW
$define _FLOW

/*

This file contains the basic definitions for equality and comparison
that is required for flow typing to work correctly. It should
therefore be included in just about every Sail specification.

*/

val eq_unit : (unit, unit) -> bool(true)

val eq_bit = pure { lem : "eq", _ : "eq_bit" } : (bit, bit) -> bool

function eq_unit(_, _) = true

val not_bool = pure {coq: "negb", _: "not"} : forall ('p : Bool). bool('p) -> bool(not('p))
/* NB: There are special cases in Sail for effectful uses of and_bool and
   or_bool that are not shown here. */

val and_bool = pure {coq: "andb", _: "and_bool"} : forall ('p : Bool) ('q : Bool). (bool('p), bool('q)) -> bool('p & 'q)

val and_bool_no_flow = pure {coq: "andb", _: "and_bool"} : (bool, bool) -> bool

val or_bool = pure {coq: "orb", _: "or_bool"} : forall ('p : Bool) ('q : Bool). (bool('p), bool('q)) -> bool('p | 'q)

val eq_int = pure {ocaml: "eq_int", interpreter: "eq_int", lem: "eq", c: "eq_int", coq: "Z.eqb"} : forall 'n 'm. (int('n), int('m)) -> bool('n == 'm)

val eq_bool = pure {ocaml: "eq_bool", interpreter: "eq_bool", lem: "eq", c: "eq_bool", coq: "Bool.eqb"} : (bool, bool) -> bool

val neq_int = pure {lem: "neq"} : forall 'n 'm. (int('n), int('m)) -> bool('n != 'm)
function neq_int (x, y) = not_bool(eq_int(x, y))

val neq_bool : (bool, bool) -> bool
function neq_bool (x, y) = not_bool(eq_bool(x, y))

val lteq_int = pure {coq: "Z.leb", _:"lteq"} : forall 'n 'm. (int('n), int('m)) -> bool('n <= 'm)
val gteq_int = pure {coq: "Z.geb", _:"gteq"} : forall 'n 'm. (int('n), int('m)) -> bool('n >= 'm)
val lt_int = pure {coq: "Z.ltb", _:"lt"} : forall 'n 'm. (int('n), int('m)) -> bool('n < 'm)
val gt_int = pure {coq: "Z.gtb", _:"gt"} : forall 'n 'm. (int('n), int('m)) -> bool('n > 'm)

overload operator == = {eq_int, eq_bit, eq_bool, eq_unit}
overload operator != = {neq_int, neq_bool}
overload operator | = {or_bool}
overload operator & = {and_bool}

overload operator <= = {lteq_int}
overload operator < = {lt_int}
overload operator >= = {gteq_int}
overload operator > = {gt_int}

/*

when we have sizeof('n) where x : int('n), we can remove that sizeof
by rewriting it to __size(x).

*/

function __id forall 'n. (x: int('n)) -> int('n) = x

overload __size = {__id}

val __deref = monadic "reg_deref" : forall ('a : Type). register('a) -> 'a

$endif
