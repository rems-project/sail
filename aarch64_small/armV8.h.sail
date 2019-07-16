/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Shaked Flur                                   */
/*  Copyright (c) 2015-2017 Kathyrn Gray                                  */
/*  All rights reserved.                                                  */
/*                                                                        */
/*  This software was developed by the University of Cambridge Computer   */
/*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  */
/*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   */
/*                                                                        */
/*  Redistribution and use in source and binary forms, with or without    */
/*  modification, are permitted provided that the following conditions    */
/*  are met:                                                              */
/*  1. Redistributions of source code must retain the above copyright     */
/*     notice, this list of conditions and the following disclaimer.      */
/*  2. Redistributions in binary form must reproduce the above copyright  */
/*     notice, this list of conditions and the following disclaimer in    */
/*     the documentation and/or other materials provided with the         */
/*     distribution.                                                      */
/*                                                                        */
/*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    */
/*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     */
/*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       */
/*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   */
/*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          */
/*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      */
/*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      */
/*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   */
/*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    */
/*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    */
/*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    */
/*  SUCH DAMAGE.                                                          */
/*========================================================================*/

type boolean = bit
type integer = int
type uinteger = nat /* ARM ARM does not have nat/uint type */
type reg_size = bits(5)
type reg_index = range(0,31)
type SIMD_index = range(0,31)

register _PC : bits(64)

/* transactional memory registers */
register TxNestingLevel : bits(8) /* same size as TXIDR_EL0.DEPTH */

bitfield TMSTATUS_type : bits(64) =
{
  /*RES0 : 63..17,*/
  IMP : 16,
  DBG : 15,
  MEM : 14,
  ERR : 13,
  INV : 12,
  SIZE : 11,
  NEST : 10,
   ABRT : 9,
   RTRY : 8,
  /*7..5 : RES0*/
  REASON : 4..0,
}
register TMAbortEffect : TMSTATUS_type /* we abuse the register write to pass out the status value */
register TMStartEffect : TMSTATUS_type /* we abuse the register read to pass in the status value */

/* abuse register write effect, instead of adding proper effects: */
register data_cache_operation_CVAU : bits(64)
register instruction_cache_operation_IVAU : bits(64)

/* General purpose registers */

register R30 : bits(64)
register R29 : bits(64)
register R28 : bits(64)
register R27 : bits(64)
register R26 : bits(64)
register R25 : bits(64)
register R24 : bits(64)
register R23 : bits(64)
register R22 : bits(64)
register R21 : bits(64)
register R20 : bits(64)
register R19 : bits(64)
register R18 : bits(64)
register R17 : bits(64)
register R16 : bits(64)
register R15 : bits(64)
register R14 : bits(64)
register R13 : bits(64)
register R12 : bits(64)
register R11 : bits(64)
register R10 : bits(64)
register R9 : bits(64)
register R8 : bits(64)
register R7 : bits(64)
register R6 : bits(64)
register R5 : bits(64)
register R4 : bits(64)
register R3 : bits(64)
register R2 : bits(64)
register R1 : bits(64)
register R0 : bits(64)

/* let _R : vector(32,dec,register(bits(64))) = */
/*   [ref undefined */
let _R : vector(31,dec,register(bits(64))) =
  [ref R30
  ,ref R29
  ,ref R28
  ,ref R27
  ,ref R26
  ,ref R25
  ,ref R24
  ,ref R23
  ,ref R22
  ,ref R21
  ,ref R20
  ,ref R19
  ,ref R18
  ,ref R17
  ,ref R16
  ,ref R15
  ,ref R14
  ,ref R13
  ,ref R12
  ,ref R11
  ,ref R10
  ,ref R9
  ,ref R8
  ,ref R7
  ,ref R6
  ,ref R5
  ,ref R4
  ,ref R3
  ,ref R2
  ,ref R1
  ,ref R0
  ]

/* val reg_index : reg_size -> UInt_reg effect pure */
/* function reg_index x = (x : (reg_index)) */

val UInt_reg : reg_size -> reg_index
function UInt_reg x = unsigned(x)

/* SIMD and floating-point registers */

register V31 : bits(128)
register V30 : bits(128)
register V29 : bits(128)
register V28 : bits(128)
register V27 : bits(128)
register V26 : bits(128)
register V25 : bits(128)
register V24 : bits(128)
register V23 : bits(128)
register V22 : bits(128)
register V21 : bits(128)
register V20 : bits(128)
register V19 : bits(128)
register V18 : bits(128)
register V17 : bits(128)
register V16 : bits(128)
register V15 : bits(128)
register V14 : bits(128)
register V13 : bits(128)
register V12 : bits(128)
register V11 : bits(128)
register V10 : bits(128)
register V9 : bits(128)
register V8 : bits(128)
register V7 : bits(128)
register V6 : bits(128)
register V5 : bits(128)
register V4 : bits(128)
register V3 : bits(128)
register V2 : bits(128)
register V1 : bits(128)
register V0 : bits(128)

/* let _V : vector(33,dec,(register(bits(128)))) = */
/*   [undefined,V31,V30,V29,V28,V27,V26,V25,V24,V23,V22, */
/*              V21,V20,V19,V18,V17,V16,V15,V14,V13,V12, */
/*              V11,V10,V9 ,V8 ,V7 ,V6 ,V5 ,V4 ,V3 ,V2 , */
/*              V1 ,V0] */

let _V : vector(32,dec,(register(bits(128)))) =
  [ref V31
  ,ref V30
  ,ref V29
  ,ref V28
  ,ref V27
  ,ref V26
  ,ref V25
  ,ref V24
  ,ref V23
  ,ref V22
  ,ref V21
  ,ref V20
  ,ref V19
  ,ref V18
  ,ref V17
  ,ref V16
  ,ref V15
  ,ref V14
  ,ref V13
  ,ref V12
  ,ref V11
  ,ref V10
  ,ref V9 
  ,ref V8 
  ,ref V7 
  ,ref V6 
  ,ref V5 
  ,ref V4 
  ,ref V3 
  ,ref V2 
  ,ref V1 
  ,ref V0
  ]


/* lsl: used instead of the ARM ARM << over integers */
val lsl : forall 'm 'n, 'm >= 0 & 'n >= 0. (int('n), int('m)) -> int('n * (2 ^ 'm)) 
function lsl (n, m) = n * (2 ^ m)

/* not_implemented is used to indicate something WE did not implement */
val not_implemented : forall ('a : Type). string -> 'a effect { escape }
function not_implemented(message) = {
  print(message);
  exit ()
}

/* not_implemented_extern is used to indicate something ARM did not define
   and we did not define yet either. Those functions used to be declared as
   external but undefined there. */
/* val not_implemented_extern : forall 'a. string -> 'a effect { escape } */
val not_implemented_extern : forall ('a : Type). string -> 'a effect { escape }
function not_implemented_extern (message) = {
  print(message);
  exit ()
}

/* info is used to convey information to the user */
val info : string -> unit effect pure
function info(message) = {
  print(message)
}

struct IMPLEMENTATION_DEFINED_type =  {
  HaveCRCExt : boolean,
  HaveAArch32EL : boolean,
  HaveAnyAArch32 : boolean,
  HaveEL2 : boolean,
  HaveEL3 : boolean,
  HighestELUsingAArch32 : boolean,
  IsSecureBelowEL3 : boolean,
}

let IMPLEMENTATION_DEFINED : IMPLEMENTATION_DEFINED_type = struct {
  HaveCRCExt = true,
  HaveAArch32EL = false,
  HaveAnyAArch32 = false,
  HaveEL2 = false,
  HaveEL3 = false,
  HighestELUsingAArch32 = false,
  IsSecureBelowEL3 = false
}

/* FIXME: ask Kathy what should we do with this */
let UNKNOWN = 0
val UNKNOWN_BITS: forall 'N, 'N >= 0. implicit('N) -> bits('N)
function UNKNOWN_BITS(N) = (replicate_bits(0b0, 'N)) : bits('N)
let UNKNOWN_BIT = b0

/* external */ val speculate_exclusive_success : unit -> bool effect {exmem}
function speculate_exclusive_success () = __excl_res ()
