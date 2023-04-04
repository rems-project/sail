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

/*** common lib ***/

enum AccType = {
  AccType_NORMAL, AccType_VEC,       /* Normal loads and stores */
  AccType_STREAM, AccType_VECSTREAM, /* Streaming loads and stores */
  AccType_ATOMIC,                    /* Atomic loads and stores */
  AccType_ORDERED,                   /* Load-Acquire and Store-Release */
  AccType_UNPRIV,                    /* Load and store unprivileged */
  AccType_IFETCH,                    /* Instruction fetch */
  AccType_PTW,                       /* Page table walk */
  /* Other operations*/
  AccType_DC,                        /* Data cache maintenance */
  AccType_IC,                        /* Instruction cache maintenance */
  AccType_AT                         /* Address translation */
}

enum MBReqDomain = 
 {MBReqDomain_Nonshareable, MBReqDomain_InnerShareable,
  MBReqDomain_OuterShareable, MBReqDomain_FullSystem}

enum MBReqTypes = 
  {MBReqTypes_Reads, MBReqTypes_Writes, MBReqTypes_All}


enum BranchType =   
  {BranchType_CALL, BranchType_ERET, BranchType_DBGEXIT,
   BranchType_RET, BranchType_JMP, BranchType_EXCEPTION,
   BranchType_UNKNOWN}

enum MoveWideOp = 
  {MoveWideOp_N, MoveWideOp_Z, MoveWideOp_K}

/* shared/functions/system/Mode_Bits */
let M32_User    = 0b10000
let M32_FIQ     = 0b10001
let M32_IRQ     = 0b10010
let M32_Svc     = 0b10011
let M32_Monitor = 0b10110
let M32_Abort   = 0b10111
let M32_Hyp     = 0b11010
let M32_Undef   = 0b11011
let M32_System  = 0b11111

/* shared/functions/system/EL0 */
let EL3 = 0b11
let EL2 = 0b10
let EL1 = 0b01
let EL0 = 0b00

enum DeviceType = 
  {DeviceType_GRE, DeviceType_nGRE, DeviceType_nGnRE, DeviceType_nGnRnE}

enum Fault = { 
  Fault_None,
  Fault_AccessFlag,
  Fault_Alignment,
  Fault_Background,
  Fault_Domain,
  Fault_Permission,
  Fault_Translation,
  Fault_AddressSize,
  Fault_SyncExternal,
  Fault_SyncExternalOnWalk,
  Fault_SyncParity,
  Fault_SyncParityOnWalk,
  Fault_AsyncParity,
  Fault_AsyncExternal,
  Fault_Debug,
  Fault_TLBConflict,
  Fault_Lockdown,
  Fault_Exclusive,
  Fault_ICacheMaint 
}

struct FaultRecord = {
  faulttype   : Fault,    /* Fault Status                             */ /* used to be called type*/
  acctype     : AccType,  /* Type of access that faulted              */
  ipaddress   : bits(48), /* Intermediate physical address            */
  s2fs1walk   : boolean,  /* Is on a Stage 1 page table walk          */
  write       : boolean,  /* TRUE for a write, FALSE for a read       */
  level       : uinteger, /* For translation, access flag and permission faults  */
  extflag     : bit,      /* IMPLEMENTATION DEFINED syndrome for external aborts */
  secondstage : boolean,  /* Is a Stage 2 abort                       */
  domain      : bits(4),  /* Domain number, AArch32 only              */
  debugmoe    : bits(4),  /* Debug method of entry, from AArch32 only */
}

struct MemAttrHints = {
  attrs : bits(2), /* The possible encodings for each attributes field are as below */
  hints : bits(2), /* The possible encodings for the hints are below */
  transient : boolean,
}

enum MemType = {MemType_Normal, MemType_Device}

struct MemoryAttributes = {
    MA_type : MemType,           /* used to be called type */

/*     DeviceType   device;      /* For Device memory types    */ */
/*     MemAttrHints inner;       /* Inner hints and attributes */ */
/*     MemAttrHints outer;       /* Outer hints and attributes */ */

    shareable : boolean,
/*     boolean      outershareable; */
}

struct FullAddress = {
    /* because we don't use TLB this is actually a virtual address and
       therefore we have to use 64 bits instead of 48 */
    physicaladdress : bits(64), /* ARM: bits(48) physicaladdress */
    NS : bit, /* '0' = Secure, '1' = Non-secure */
}

struct AddressDescriptor = {
    fault : FaultRecord, /* fault.type indicates whether the address is valid */
    memattrs : MemoryAttributes,
    paddress : FullAddress,
}

enum PrefetchHint = {Prefetch_READ, Prefetch_WRITE, Prefetch_EXEC}

val ASR_C : forall 'N 'S, 'N >= 1 & 'S >= 1. (bits('N),int('S)) -> (bits('N), bit) effect {escape}
val LSL_C : forall 'N 'S, 'N >= 0 & 'S >= 1. (bits('N),int('S)) -> (bits('N), bit) effect pure
val LSR_C : forall 'N 'S, 'N >= 1 & 'S >= 1. (bits('N),int('S)) -> (bits('N), bit) effect pure
val ROR_C : forall 'N 'S, 'N >= 1 & 'S != 0. (bits('N),int('S)) -> (bits('N), bit) effect pure
val IsZero : forall 'N, 'N >=0. bits('N) -> boolean effect pure
val Replicate : forall 'N 'M, 'N >='M & 'M >=0. (implicit('N),bits('M)) -> bits('N) effect {escape}
val SignExtend : forall 'N 'M, 'N > 'M & 'M >= 1. (implicit('N),bits('M)) -> bits('N) effect {escape}
val ZeroExtend : forall 'N 'M, 'N >= 'M & 'M >= 0. (implicit('N),bits('M)) -> bits('N) effect pure
val Zeros : forall 'N, 'N >=0. implicit('N) -> bits('N) effect pure
val Ones : forall 'N, 'N >=1. implicit('N) -> bits('N) effect {escape}
/* val UInt : forall Nat 'N, Nat 'M, 'M = 2**'N. bits('N) -> [|'M + -1|] effect pure */
val UInt : forall 'N, 'N >=0 . bits('N) -> range(0, 2 ^ 'N + -1) effect {escape}
/* val UInt : forall 'N 'M, 'N >=0 & 'M >= 0. bits('N) -> Int('M) effect pure */
/* val SInt : forall Nat 'N, Nat 'M, Nat 'K, 'M = 'N + -1, 'K = 2**'M. bits('N) -> [|'K * -1:'K + -1|] effect pure */
val SInt : forall 'N, 'N > 0. bits('N) -> range(-(2 ^ ('N - 1)), 2 ^ ('N - 1) - 1) effect pure
val HighestSetBit : forall 'N, 'N >= 0. bits('N) -> option(range(0,'N - 1)) effect pure
val CountLeadingZeroBits : forall 'N, 'N >= 0. bits('N) -> range(0,'N) effect pure
val IsSecure : unit -> boolean effect {escape,rreg}
val IsSecureBelowEL3 : unit -> boolean effect {escape,rreg}
val SCR_GEN : unit -> SCRType effect {escape,rreg}
val UsingAArch32 : unit -> boolean effect pure
val ELUsingAArch32 : bits(2) -> boolean effect pure
val Halted : unit -> boolean effect {rreg}
val HaveEL : bits(2) -> boolean effect {escape}
val HaveAnyAArch32 : unit -> boolean effect pure
val HighestELUsingAArch32 : unit -> boolean effect pure
val Hint_Branch : BranchType -> unit effect pure

/*************************************************************************/
/*** AArch64 lib ***/

enum CountOp = {CountOp_CLZ, CountOp_CLS, CountOp_CNT}

enum ExtendType = 
  { ExtendType_SXTB, ExtendType_SXTH, ExtendType_SXTW, ExtendType_SXTX,
    ExtendType_UXTB, ExtendType_UXTH, ExtendType_UXTW, ExtendType_UXTX }

enum RevOp = {RevOp_RBIT, RevOp_REV16, RevOp_REV32, RevOp_REV64}

enum ShiftType =   /* the order is important for decoding */
  {ShiftType_LSL, ShiftType_LSR, ShiftType_ASR, ShiftType_ROR}

enum LogicalOp = {LogicalOp_AND, LogicalOp_EOR, LogicalOp_ORR}

enum MemOp = {MemOp_LOAD, MemOp_STORE, MemOp_PREFETCH}

enum MemBarrierOp = {MemBarrierOp_DSB, MemBarrierOp_DMB, MemBarrierOp_ISB}

enum SystemHintOp = 
  {SystemHintOp_NOP, SystemHintOp_YIELD,
   SystemHintOp_WFE, SystemHintOp_WFI,
   SystemHintOp_SEV, SystemHintOp_SEVL}

enum PSTATEField = 
  {PSTATEField_DAIFSet, PSTATEField_DAIFClr, PSTATEField_SP}

enum SystemOp = {Sys_AT, Sys_DC, Sys_IC, Sys_TLBI, Sys_SYS}

enum DCOp = {IVAC, ISW, CSW, CISW, ZVA, CVAC, CVAU, CIVAC}

enum ICOp = {IALLUIS, IALLU, IVAU}


val rPC : unit -> bits(64) effect {rreg}
val rSP : forall 'N, 'N in {8,16,32,64}. implicit('N) -> bits('N) effect {rreg,escape}
val wX : forall 'N, 'N in {8,16,32,64}. (reg_index,bits('N)) -> unit effect {wreg}
val rX : forall 'N, 'N in {8,16,32,64}. (implicit('N),reg_index) -> bits('N) effect {rreg}
val wV : forall 'N, 'N in {8,16,32,64,128}. (SIMD_index,bits('N)) -> unit effect {wreg}
val rV : forall 'N, 'N in {8,16,32,64,128}. (implicit('N),SIMD_index) -> bits('N) effect {rreg}
val rVpart : forall 'N, 'N in {8,16,32,64,128}. (implicit('N),SIMD_index,range(0,1)) -> bits('N) effect {rreg,escape}
val SCTLR' : unit -> SCTLR_type effect {rreg,escape}
val AArch64_UndefinedFault : unit -> unit effect {escape}
val AArch64_TranslateAddress : (bits(64),AccType,boolean,boolean,uinteger) -> AddressDescriptor effect pure
val AArch64_WFxTrap : (bits(2),boolean) -> unit effect {escape}
val AArch64_AlignmentFault : (AccType,boolean,boolean) -> FaultRecord effect pure
val AArch64_ResetGeneralRegisters : unit -> unit effect {wreg}
val AArch64_ResetSIMDFPRegisters : unit -> unit effect {wreg}
val AArch64_ResetSpecialRegisters : unit -> unit effect {wreg,escape}
val AArch64_IsExclusiveVA : (bits(64),integer,uinteger) -> boolean effect pure

/*************************************************************************/
/*** AArch32 lib ***/



