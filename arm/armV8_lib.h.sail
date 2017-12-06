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

(*** common lib ***)

typedef AccType =
  enumerate {AccType_NORMAL; AccType_VEC;       (* Normal loads and stores *)
             AccType_STREAM; AccType_VECSTREAM; (* Streaming loads and stores *)
             AccType_ATOMIC;                    (* Atomic loads and stores *)
             AccType_ORDERED;                   (* Load-Acquire and Store-Release *)
             AccType_UNPRIV;                    (* Load and store unprivileged *)
             AccType_IFETCH;                    (* Instruction fetch *)
             AccType_PTW;                       (* Page table walk *)
             (* Other operations*)
             AccType_DC;                        (* Data cache maintenance *)
             AccType_IC;                        (* Instruction cache maintenance *)
             AccType_AT}                        (* Address translation *)

typedef MBReqDomain =
  enumerate {MBReqDomain_Nonshareable; MBReqDomain_InnerShareable;
             MBReqDomain_OuterShareable; MBReqDomain_FullSystem}

typedef MBReqTypes =
 enumerate {MBReqTypes_Reads; MBReqTypes_Writes; MBReqTypes_All}


typedef BranchType =
  enumerate {BranchType_CALL; BranchType_ERET; BranchType_DBGEXIT;
             BranchType_RET; BranchType_JMP; BranchType_EXCEPTION;
             BranchType_UNKNOWN}

typedef MoveWideOp =
  enumerate {MoveWideOp_N; MoveWideOp_Z; MoveWideOp_K}

(* shared/functions/system/Mode_Bits *)
let M32_User    = 0b10000
let M32_FIQ     = 0b10001
let M32_IRQ     = 0b10010
let M32_Svc     = 0b10011
let M32_Monitor = 0b10110
let M32_Abort   = 0b10111
let M32_Hyp     = 0b11010
let M32_Undef   = 0b11011
let M32_System  = 0b11111

(* shared/functions/system/EL0 *)
let EL3 = 0b11
let EL2 = 0b10
let EL1 = 0b01
let EL0 = 0b00

typedef DeviceType = enumerate {DeviceType_GRE; DeviceType_nGRE;
                                DeviceType_nGnRE; DeviceType_nGnRnE}

typedef Fault =
  enumerate { Fault_None;
              Fault_AccessFlag;
              Fault_Alignment;
              Fault_Background;
              Fault_Domain;
              Fault_Permission;
              Fault_Translation;
              Fault_AddressSize;
              Fault_SyncExternal;
              Fault_SyncExternalOnWalk;
              Fault_SyncParity;
              Fault_SyncParityOnWalk;
              Fault_AsyncParity;
              Fault_AsyncExternal;
              Fault_Debug;
              Fault_TLBConflict;
              Fault_Lockdown;
              Fault_Exclusive;
              Fault_ICacheMaint }

typedef FaultRecord = const struct {
  Fault      type;        (* Fault Status                             *)
  AccType    acctype;     (* Type of access that faulted              *)
  bit[48]    ipaddress;   (* Intermediate physical address            *)
  boolean    s2fs1walk;   (* Is on a Stage 1 page table walk          *)
  boolean    write;       (* TRUE for a write, FALSE for a read       *)
  uinteger   level;       (* For translation, access flag and permission faults  *)
  bit        extflag;     (* IMPLEMENTATION DEFINED syndrome for external aborts *)
  boolean    secondstage; (* Is a Stage 2 abort                       *)
  bit[4]     domain;      (* Domain number, AArch32 only              *)
  bit[4]     debugmoe;    (* Debug method of entry, from AArch32 only *)
}

typedef MemAttrHints = const struct {
    bit[2]  attrs; (* The possible encodings for each attributes field are as below *)
    bit[2]  hints; (* The possible encodings for the hints are below *)
    boolean transient;
}

typedef MemType = enumerate {MemType_Normal; MemType_Device}

typedef MemoryAttributes = const struct {
    MemType      type;

(*     DeviceType   device;      (* For Device memory types    *) *)
(*     MemAttrHints inner;       (* Inner hints and attributes *) *)
(*     MemAttrHints outer;       (* Outer hints and attributes *) *)

    boolean      shareable;
(*     boolean      outershareable; *)
}

typedef FullAddress = const struct {
    (* because we don't use TLB this is actually a virtual address and
       therefore we have to use 64 bits instead of 48 *)
    bit[64] physicaladdress; (* ARM: bit[48] physicaladdress *)
    bit     NS; (* '0' = Secure, '1' = Non-secure *)
}

typedef AddressDescriptor = const struct {
    FaultRecord      fault; (* fault.type indicates whether the address is valid *)
    MemoryAttributes memattrs;
    FullAddress      paddress;
}

typedef PrefetchHint =
  enumerate {Prefetch_READ; Prefetch_WRITE; Prefetch_EXEC}

val forall Nat 'N, Nat 'S, 'S >= 1. (bit['N],[:'S:]) -> (bit['N], bit) effect pure ASR_C
val forall Nat 'N, Nat 'S, 'S >= 1. (bit['N],[:'S:]) -> (bit['N], bit) effect pure LSL_C
val forall Nat 'N, Nat 'S, 'S >= 1. (bit['N],[:'S:]) -> (bit['N], bit) effect pure LSR_C
val forall Nat 'N, Nat 'S, 'S >= 1, 'S <= -1. (bit['N],[:'S:]) -> (bit['N], bit) effect pure ROR_C
val forall Nat 'N. bit['N] -> boolean effect pure IsZero
val forall Nat 'N, Nat 'M. (implicit<'N>,bit['M]) -> bit['N] effect pure Replicate
val forall Nat 'N, Nat 'M, 'N >= 'M. (implicit<'N>,bit['M]) -> bit['N] effect pure SignExtend
val forall Nat 'N, Nat 'M, 'N >= 'M. (implicit<'N>,bit['M]) -> bit['N] effect pure ZeroExtend
val forall Nat 'N. implicit<'N> -> bit['N] effect pure Zeros
val forall Nat 'N. implicit<'N> -> bit['N] effect pure Ones
(* val forall Nat 'N, Nat 'M, 'M = 2**'N. bit['N] -> [|'M + -1|] effect pure UInt *)
val forall Nat 'N, Nat 'M. bit['N] -> [:'M:] effect pure UInt
(* val forall Nat 'N, Nat 'M, Nat 'K, 'M = 'N + -1, 'K = 2**'M. bit['N] -> [|'K * -1:'K + -1|] effect pure SInt *)
val forall Nat 'N, Nat 'M. bit['N] -> [:'M:] effect pure SInt
val forall Nat 'N. bit['N+1] -> option<[|0:'N + -1|]> effect pure HighestSetBit
val forall Nat 'N. bit['N] -> [|'N|] effect pure CountLeadingZeroBits
val unit -> boolean effect {rreg} IsSecure
val unit -> boolean effect {rreg} IsSecureBelowEL3
val unit -> SCRType effect pure SCR_GEN
val unit -> boolean effect pure UsingAArch32
val bit[2] -> boolean effect pure ELUsingAArch32
val unit -> boolean effect {rreg} Halted
val bit[2] -> boolean effect pure HaveEL
val unit -> boolean effect pure HaveAnyAArch32
val unit -> boolean effect pure HighestELUsingAArch32
val unit -> unit effect pure Unreachable
val BranchType -> unit effect pure Hint_Branch

(*************************************************************************)
(*** AArch64 lib ***)

typedef CountOp =
  enumerate {CountOp_CLZ; CountOp_CLS; CountOp_CNT}

typedef ExtendType =
  enumerate { ExtendType_SXTB; ExtendType_SXTH; ExtendType_SXTW; ExtendType_SXTX;
              ExtendType_UXTB; ExtendType_UXTH; ExtendType_UXTW; ExtendType_UXTX }

typedef RevOp =
  enumerate {RevOp_RBIT; RevOp_REV16; RevOp_REV32; RevOp_REV64}

typedef ShiftType =
  (* the oreder is important for decoding *)
  enumerate {ShiftType_LSL; ShiftType_LSR; ShiftType_ASR; ShiftType_ROR}

typedef LogicalOp =
  enumerate {LogicalOp_AND; LogicalOp_EOR; LogicalOp_ORR}

typedef MemOp =
  enumerate {MemOp_LOAD; MemOp_STORE; MemOp_PREFETCH}

typedef MemBarrierOp =
  enumerate {MemBarrierOp_DSB; MemBarrierOp_DMB; MemBarrierOp_ISB}

typedef SystemHintOp =
  enumerate {SystemHintOp_NOP; SystemHintOp_YIELD;
             SystemHintOp_WFE; SystemHintOp_WFI;
             SystemHintOp_SEV; SystemHintOp_SEVL}

typedef PSTATEField =
  enumerate {PSTATEField_DAIFSet; PSTATEField_DAIFClr;
             PSTATEField_SP}

val unit -> bit[64] effect {rreg} rPC
val forall Nat 'N, 'N IN {8,16,32,64}. implicit<'N> -> bit['N] effect {rreg} rSP
val forall Nat 'N, 'N IN {32,64}. (reg_index,bit['N]) -> unit effect {wreg} wX
val forall Nat 'N, 'N IN {8,16,32,64}. (implicit<'N>,reg_index) -> bit['N] effect {rreg} rX
val forall Nat 'N, 'N IN {8,16,32,64,128}. (SIMD_index,bit['N]) -> unit effect {wreg} wV
val forall Nat 'N, 'N IN {8,16,32,64,128}. (implicit<'N>,SIMD_index) -> bit['N] effect {rreg} rV
val forall Nat 'N, 'N IN {8,16,32,64,128}. (implicit<'N>,SIMD_index,[|1|]) -> bit['N] effect {rreg} rVpart
val unit -> SCTLR_type effect {rreg} SCTLR'
val unit -> unit effect {escape} AArch64_UndefinedFault
val (bit[64],AccType,boolean,boolean,uinteger) -> AddressDescriptor effect pure AArch64_TranslateAddress
val (bit[2],boolean) -> unit effect {escape} AArch64_WFxTrap
val (AccType,boolean,boolean) -> FaultRecord effect pure AArch64_AlignmentFault
val unit -> unit effect {wreg} AArch64_ResetGeneralRegisters
val unit -> unit effect {wreg} AArch64_ResetSIMDFPRegisters
val unit -> unit effect {wreg} AArch64_ResetSpecialRegisters
val (bit[64],integer,uinteger) -> boolean effect pure AArch64_IsExclusiveVA

(*************************************************************************)
(*** AArch32 lib ***)



