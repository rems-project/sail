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

$ifndef _ISLA
$define _ISLA

$ifdef SYMBOLIC

val isla_reset_registers = pure "reset_registers" : unit -> unit

val isla_log_event = pure "log_event" : forall ('a: Type). (string, 'a) -> unit

val isla_synchronize_registers = pure "synchronize_registers" : unit -> unit

val isla_mark_register = pure "mark_register" : forall ('a: Type). (register('a), string) -> unit

val isla_mark_register_pair = pure "mark_register_pair" : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

val isla_monomorphize = pure "monomorphize" : forall 'n, 'n >= 0. bits('n) -> bits('n)

$else

val isla_reset_registers : unit -> unit

function isla_reset_registers() = ()

val isla_log_event : forall ('a: Type). (string, 'a) -> unit

function isla_log_event(_, _) = ()

val isla_synchronize_registers : unit -> unit

function isla_synchronize_registers() = ()

val isla_mark_register : forall ('a: Type). (register('a), string) -> unit

function isla_mark_register(_, _) = ()

val isla_mark_register_pair : forall ('a: Type) ('b: Type). (register('a), register('b), string) -> unit

function isla_mark_register_pair(_, _, _) = ()

val isla_monomorphize : forall 'n, 'n >= 0. bits('n) -> bits('n)

function isla_monomorphize bv = bv

$endif

val isla_ignore_write_to : forall ('a: Type). register('a) -> unit

function isla_ignore_write_to(reg) = isla_mark_register(reg, "ignore_write")

$endif
