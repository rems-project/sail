(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Shaked Flur                                   *)
(*  Copyright (c) 2015-2017 Kathyrn Gray                                  *)
(*  All rights reserved.                                                  *)
(*                                                                        *)
(*  This software was developed by the University of Cambridge Computer   *)
(*  Laboratory as part of the Rigorous Engineering of Mainstream Systems  *)
(*  (REMS) project, funded by EPSRC grant EP/K008528/1.                   *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*     notice, this list of conditions and the following disclaimer.      *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*     notice, this list of conditions and the following disclaimer in    *)
(*     the documentation and/or other materials provided with the         *)
(*     distribution.                                                      *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''    *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED     *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A       *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR   *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,          *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT      *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF      *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND   *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,    *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT    *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF    *)
(*  SUCH DAMAGE.                                                          *)
(*========================================================================*)

default Order dec

typedef boolean = bit
typedef integer = int
typedef uinteger = nat (* ARM ARM does not have nat/uint type *)
typedef reg_size   = bit[5]
typedef reg_index = [|31|]
typedef SIMD_index = [|32|]

register (bit[64])  _PC

(* transactional memory registers *)
register (bit[8]) TxNestingLevel (* same size as TXIDR_EL0.DEPTH *)

typedef TMSTATUS_type = register bits [63:0]
{
  (*63..17 : RES0;*)
  16 : IMP;
  15 : DBG;
  14 : MEM;
  13 : ERR;
  12 : INV;
  11 : SIZE;
  10 : NEST;
   9 : ABRT;
   8 : RTRY;
  (*7..5 : RES0*)
  4..0 : REASON;
}
register (TMSTATUS_type) TMAbortEffect (* we abuse the register write to pass out the status value *)
register (TMSTATUS_type) TMStartEffect (* we abuse the register read to pass in the status value *)

(* General purpose registers *)

register (bit[64]) R30
register (bit[64]) R29
register (bit[64]) R28
register (bit[64]) R27
register (bit[64]) R26
register (bit[64]) R25
register (bit[64]) R24
register (bit[64]) R23
register (bit[64]) R22
register (bit[64]) R21
register (bit[64]) R20
register (bit[64]) R19
register (bit[64]) R18
register (bit[64]) R17
register (bit[64]) R16
register (bit[64]) R15
register (bit[64]) R14
register (bit[64]) R13
register (bit[64]) R12
register (bit[64]) R11
register (bit[64]) R10
register (bit[64]) R9
register (bit[64]) R8
register (bit[64]) R7
register (bit[64]) R6
register (bit[64]) R5
register (bit[64]) R4
register (bit[64]) R3
register (bit[64]) R2
register (bit[64]) R1
register (bit[64]) R0

let (vector<31,32,dec,(register<bit[64]>)>) _R =
  [undefined,R30,R29,R28,R27,R26,R25,R24,R23,R22,R21,
             R20,R19,R18,R17,R16,R15,R14,R13,R12,R11,
             R10,R9 ,R8 ,R7 ,R6 ,R5 ,R4 ,R3 ,R2 ,R1 ,
             R0]

function reg_index effect pure UInt_reg((reg_size) x) = (reg_index) x

(* SIMD and floating-point registers *)

register (bit[128]) V31
register (bit[128]) V30
register (bit[128]) V29
register (bit[128]) V28
register (bit[128]) V27
register (bit[128]) V26
register (bit[128]) V25
register (bit[128]) V24
register (bit[128]) V23
register (bit[128]) V22
register (bit[128]) V21
register (bit[128]) V20
register (bit[128]) V19
register (bit[128]) V18
register (bit[128]) V17
register (bit[128]) V16
register (bit[128]) V15
register (bit[128]) V14
register (bit[128]) V13
register (bit[128]) V12
register (bit[128]) V11
register (bit[128]) V10
register (bit[128]) V9
register (bit[128]) V8
register (bit[128]) V7
register (bit[128]) V6
register (bit[128]) V5
register (bit[128]) V4
register (bit[128]) V3
register (bit[128]) V2
register (bit[128]) V1
register (bit[128]) V0

let (vector<32,33,dec,(register<bit[128]>)>) _V =
  [undefined,V31,V30,V29,V28,V27,V26,V25,V24,V23,V22,
             V21,V20,V19,V18,V17,V16,V15,V14,V13,V12,
             V11,V10,V9 ,V8 ,V7 ,V6 ,V5 ,V4 ,V3 ,V2 ,
             V1 ,V0]


(* lsl: used instead of the ARM ARM << over integers *)
function forall Nat 'm, Nat 'n, 'm >= 0, 'n >= 0. [:'n * 2** 'm:] lsl(([:'n:]) n, ([:'m:]) m) = n * (2 ** m)

(* not_implemented is used to indicate something WE did not implement *)
function unit effect { escape } not_implemented((string) message) =
{
  exit message;
}

(* not_implemented_extern is used to indicate something ARM did not define
   and we did not define yet either. Those functions used to be declared as
   external but undefined there. *)
function forall 'a. 'a effect { escape } not_implemented_extern((string) message) =
{
  exit message;
}

(* info is used to convey information to the user *)
function unit effect pure info((string) message) = ()

typedef IMPLEMENTATION_DEFINED_type = const struct
{
  boolean HaveCRCExt;
  boolean HaveAArch32EL;
  boolean HaveAnyAArch32;
  boolean HaveEL2;
  boolean HaveEL3;
  boolean HighestELUsingAArch32;
  boolean IsSecureBelowEL3;
}
let IMPLEMENTATION_DEFINED =
{
  HaveCRCExt = true;
  HaveAArch32EL = false;
  HaveAnyAArch32 = false;
  HaveEL2 = false;
  HaveEL3 = false;
  HighestELUsingAArch32 = false;
  IsSecureBelowEL3 = false;
}

(* FIXME: ask Kathy what should we do with this *)
let UNKNOWN = 0


val extern unit -> bool effect {exmem} speculate_exclusive_success
