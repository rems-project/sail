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
val __id = pure { systemverilog: "id" } : forall 'n. int('n) -> int('n)

function __id(x) = x

overload __size = {__id}

val __deref = impure "reg_deref" : forall ('a : Type). register('a) -> 'a

val lteq_int = pure { coq: "Z.leb", lean: "_lean_le", _: "lteq" } : forall 'n 'm. (int('n), int('m)) -> bool('n <= 'm)

val gteq_int = pure { coq: "Z.geb", lean: "_lean_ge", _: "gteq" } : forall 'n 'm. (int('n), int('m)) -> bool('n >= 'm)

val lt_int = pure { coq: "Z.ltb", lean: "_lean_lt", _: "lt" } : forall 'n 'm. (int('n), int('m)) -> bool('n < 'm)

val gt_int = pure { coq: "Z.gtb", lean: "_lean_gt", _: "gt" } : forall 'n 'm. (int('n), int('m)) -> bool('n > 'm)
