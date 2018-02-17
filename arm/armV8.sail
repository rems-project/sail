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

typedef ast = const union forall Nat 'R, 'R IN {32, 64},     (* register size *)
                                 Nat 'D, 'D IN {8,16,32,64}. (* data size *)
{
  Unallocated;
  (boolean) ImplementationDefinedTestBeginEnd;
  ImplementationDefinedStopFetching;
  ImplementationDefinedThreadStart;

  (* transactional memory, not part of the official spec *)
  (reg_index) TMStart;
  TMCommit;
  (boolean,bit[5]) TMAbort;
  TMTest;

  (reg_index,[:'R:],boolean,bit[64]) CompareAndBranch;
  (bit[64],bit[4]) BranchConditional;
  (bit[16]) GenerateExceptionEL1; (* TODO: add to .hgen *)
  (bit[16]) GenerateExceptionEL2; (* TODO: add to .hgen *)
  (bit[16]) GenerateExceptionEL3; (* TODO: add to .hgen *)
  (bit[16]) DebugBreakpoint; (* TODO: add to .hgen *)
  ExternalDebugBreakpoint; (* TODO: add to .hgen *)
  (bit[2]) DebugSwitchToExceptionLevel; (* TODO: add to .hgen *)
  (bit[4],PSTATEField) MoveSystemImmediate;
  (SystemHintOp) Hint;
  (uinteger) ClearExclusiveMonitor;
  (MemBarrierOp,MBReqDomain,MBReqTypes) Barrier;
  (reg_index,uinteger,uinteger,uinteger,uinteger,uinteger,boolean) System;
  (reg_index,uinteger,uinteger,uinteger,uinteger,uinteger,boolean) MoveSystemRegister;
  (reg_index,[:'R:],uinteger,bit,bit[64]) TestBitAndBranch;
  (BranchType,bit[64]) BranchImmediate;
  (reg_index,BranchType) BranchRegister;
  ExceptionReturn; (* TODO: add to .hgen *)
  DebugRestorePState; (* TODO: add to .hgen *)
  (reg_index,MemOp,boolean,uinteger,bit[64],[:'D:]) LoadLiteral;
  (reg_index,reg_index,reg_index,reg_index,AccType,boolean,boolean,MemOp,uinteger,[:'R:],[:'D:]) LoadStoreAcqExc;
  (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,uinteger,[:'D:],bit[64]) LoadStorePairNonTemp;
  (reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,bit[64],[:'R:],[:'D:]) LoadImmediate;
  (reg_index,reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,ExtendType,uinteger,[:'R:],[:'D:]) LoadRegister;
  (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,boolean,[:'D:],bit[64]) LoadStorePair;
  (reg_index,reg_index,[:'R:],boolean,boolean,bit['R]) AddSubImmediate;
  (reg_index,reg_index,[:'R:],boolean,boolean,uinteger,uinteger,bit['R],bit['R]) BitfieldMove;
  (reg_index,reg_index,reg_index,[:'R:],uinteger) ExtractRegister;
  (reg_index,reg_index,[:'R:],boolean,LogicalOp,bit['R]) LogicalImmediate;
  (reg_index,[:'R:],bit[16],uinteger,MoveWideOp) MoveWide;
  (reg_index,boolean,bit[64]) Address;
  (reg_index,reg_index,reg_index,[:'R:],boolean,boolean,ExtendType,[|7|]) AddSubExtendRegister;
  (reg_index,reg_index,reg_index,[:'R:],boolean,boolean,ShiftType,[|63|]) AddSubShiftedRegister;
  (reg_index,reg_index,reg_index,[:'R:],boolean,boolean) AddSubCarry;
  (reg_index,[:'R:],boolean,bit[4],bit[4],bit['R]) ConditionalCompareImmediate;
  (reg_index,reg_index,[:'R:],boolean,bit[4],bit[4]) ConditionalCompareRegister;
  (reg_index,reg_index,reg_index,[:'R:],bit[4],boolean,boolean) ConditionalSelect;
  (reg_index,reg_index,[:'R:],RevOp) Reverse;
  (reg_index,reg_index,[:'R:],CountOp) CountLeading;
  (reg_index,reg_index,reg_index,[:'R:],boolean) Division;
  (reg_index,reg_index,reg_index,[:'R:],ShiftType) Shift;
  (reg_index,reg_index,reg_index,[:'D:],boolean) CRC;
  (reg_index,reg_index,reg_index,reg_index,[:'R:],[:'D:],boolean) MultiplyAddSub;
  (reg_index,reg_index,reg_index,reg_index,[:'R:],[:'D:],boolean,boolean) MultiplyAddSubLong;
  (reg_index,reg_index,reg_index,reg_index,[:'R:],[:'D:],boolean) MultiplyHigh;
  (reg_index,reg_index,reg_index,[:'R:],boolean,LogicalOp,ShiftType,[|63|],boolean) LogicalShiftedRegister;
}

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}. ast<'R,'D> -> unit effect {rreg,wreg,rmem,barr,eamem,wmv,exmem,escape} execute
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}. unit execute

(* TSTART - dummy decoding *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeTMStart ((bit[5]) Rt) =
{
  (reg_index) t := UInt_reg(Rt);

  Some(TMStart(t));
}

(* transactional memory, not part of the official spec *)
function clause execute (TMStart(t)) = {
  (bit[8]) nesting := TxNestingLevel;

  if nesting <_u TXIDR_EL0.DEPTH then {
    TxNestingLevel := nesting + 1;
    (bit[64]) status := 0;
    if nesting == 0 then
      status := TMStartEffect; (* fake effect *)
    wX(t) := status;
  } else {
    (bit[64]) status := 0;
    status[10] := 1; (* set the NEST bit *)
    TMAbortEffect := status; (* fake effect *)
  }
}

val extern unit -> unit effect {barr} TMCommitEffect

(* TCOMMIT - dummy decoding *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeTMCommit () =
{
  Some(TMCommit);
}

(* transactional memory, not part of the official spec *)
function clause execute (TMCommit) = {
  (bit[8]) nesting := TxNestingLevel;

  if nesting == 1 then
    TMCommitEffect() (* fake effect *)
  else if nesting == 0 then
    AArch64_UndefinedFault();

  TxNestingLevel := nesting - 1;
}

(* TTEST - dummy decoding *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeTMTest () =
{
  Some(TMTest);
}

(* transactional memory, not part of the official spec *)
function clause execute (TMTest) = {
  if TxNestingLevel > 0 then
    wPSTATE_NZCV() := 0b0000
  else
    wPSTATE_NZCV() := 0b0100
}

(* TABORT - dummy decoding *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeTMAbort ([R]:(bit[5]) imm5) =
{
  Some(TMAbort(R,imm5));
}

(* transactional memory, not part of the official spec *)
function clause execute (TMAbort(retry,reason)) = {
  if TxNestingLevel > 0 then {
    (bit[64]) status := 0;
    status[4..0] := reason; (* REASON *)
    status[8] := retry; (* RTRY *)
    status[9] := 1; (* ABRT *)
    TMAbortEffect := status; (* fake effect *)
  };
}

(* CBNZ *)
(* CBZ *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeCompareBranchImmediate ([sf]:0b011010:[op]:(bit[19]) imm19:Rt) =
{
  (reg_index) t := UInt_reg(Rt);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) iszero := (op == 0);
  (bit[64]) offset := SignExtend(imm19:0b00);

  Some(CompareAndBranch(t,datasize,iszero,offset));
}

function clause execute (CompareAndBranch(t,datasize,iszero,offset)) = {
  (bit['R]) operand1 := rX(t);
  if IsZero(operand1) == iszero then
    BranchTo(rPC() + offset, BranchType_JMP);
}

(* B.cond *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeConditionalBranchImmediate (0b0101010:0b0:(bit[19]) imm19:0b0:_cond) =
{
  (bit[64]) offset := SignExtend(imm19:0b00);
  (bit[4]) condition := _cond;

  Some(BranchConditional(offset,condition));
}

function clause execute (BranchConditional(offset,condition)) = {
  if ConditionHolds(condition) then
    BranchTo(rPC() + offset, BranchType_JMP);
}


val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect {escape} decodeExceptionGeneration
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeExceptionGeneration

(* SVC *)
function clause decodeExceptionGeneration (0b11010100:0b000:(bit[16]) imm16:0b000:0b01) =
{
  (bit[16]) imm := imm16;

  Some(GenerateExceptionEL1(imm))
}

function clause execute (GenerateExceptionEL1(imm)) =
{
  AArch64_CallSupervisor(imm);
}

(* HVC *)
function clause decodeExceptionGeneration (0b11010100:0b000:(bit[16]) imm16:0b000:0b10) = {
  (bit[16]) imm := imm16;

  Some(GenerateExceptionEL2(imm))
}

function clause execute (GenerateExceptionEL2(imm)) =
{
  if ~(HaveEL(EL2)) | PSTATE_EL == EL0 | (PSTATE_EL == EL1 & IsSecure()) then
    UnallocatedEncoding();

  (bit) hvc_enable := if HaveEL(EL3) then SCR_EL3.HCE else NOT'(HCR_EL2.HCD);
  if hvc_enable == 0 then
    AArch64_UndefinedFault()
  else
    AArch64_CallHypervisor(imm);
}

(* SMC *)
function clause decodeExceptionGeneration (0b11010100:0b000:(bit[16]) imm16:0b000:0b11) = {
  (bit[16]) imm := imm16;

  Some(GenerateExceptionEL3(imm))
}

function clause execute (GenerateExceptionEL3(imm)) =
{
  if ~(HaveEL(EL3)) | PSTATE_EL == EL0 then
    UnallocatedEncoding();

  AArch64_CheckForSMCTrap(imm);

  if SCR_EL3.SMD == 1 then
    (* SMC disabled *)
    AArch64_UndefinedFault()
  else
    AArch64_CallSecureMonitor(imm);
}

(* BRK *)
function clause decodeExceptionGeneration (0b11010100:0b001:(bit[16]) imm16:0b000:0b00) = {
  (bit[16]) comment := imm16;

  Some(DebugBreakpoint(comment))
}

function clause execute (DebugBreakpoint(comment)) =
{
  AArch64_SoftwareBreakpoint(comment);
}

(* HLT *)
function clause decodeExceptionGeneration (0b11010100:0b010:(bit[16]) imm16:0b000:0b00) =
{
  (* FIXME: we don't allow register reads in the decoding, but we probably should *)
  (* ARM: if EDSCR.HDE == 0 | ~(HaltingAllowed()) then AArch64_UndefinedFault(); (* ARM: UndefinedFault() *) *)

  Some(ExternalDebugBreakpoint);
}


function clause execute (ExternalDebugBreakpoint) =
{
  Halt(DebugHalt_HaltInstruction);
}

(* DCPS1 LL=0b01*)
(* DCPS2 LL=0b10*)
(* DCPS3 LL=0b11*)
function clause decodeExceptionGeneration (0b11010100:0b101:(bit[16]) imm16:0b000:(bit[2]) LL) =
{
  (bit[2]) target_level := LL;
  if LL == 0b00 then UnallocatedEncoding();
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: if ~(Halted()) then AArch64_UndefinedFault(); *)

  Some(DebugSwitchToExceptionLevel(target_level));
}

function clause execute (DebugSwitchToExceptionLevel(target_level)) =
{
  DCPSInstruction(target_level);
}

end decodeExceptionGeneration

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect {escape} decodeSystem
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeSystem

(* MSR (immediate) *)
function clause decodeSystem (0b1101010100:[0]:0b00:(bit[3]) op1:0b0100:CRm:(bit[3]) op2:0b11111) = {
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: CheckSystemAccess(0b00, op1, 0b0100, CRm, op2, 0b11111, 0); *)

  (bit[4]) operand := CRm;
  (PSTATEField) field := 0; (* ARM: uninitialized *)
  switch (op1:op2) {
    case (0b000:0b101) -> field := PSTATEField_SP
    case (0b011:0b110) -> field := PSTATEField_DAIFSet
    case (0b011:0b111) -> field := PSTATEField_DAIFClr
    case _ -> UnallocatedEncoding()
  };

  (* FIXME: we don't allow register reads in the decoding *)
  (* FIXME: it is not clear why this check is here. How is it different
            than the CheckSystemAccess above? *)
  (*Check that an AArch64 MSR/MRS access to the DAIF flags is permitted*)
  (* ARM: if op1 == 0b011 & PSTATE_EL == EL0 & SCTLR_EL1.UMA == 0 then
    AArch64_SystemRegisterTrap(EL1, 0b00, op2, op1, 0b0100, 0b11111, CRm, 0);*)

  Some(MoveSystemImmediate(operand,field));
}

function clause execute ( MoveSystemImmediate(operand,field) ) = {
  switch field {
    case PSTATEField_SP -> PSTATE_SP := operand[0]
    case PSTATEField_DAIFSet -> {
      PSTATE_D := (PSTATE_D | operand[3]);
      PSTATE_A := (PSTATE_A | operand[2]);
      PSTATE_I := (PSTATE_I | operand[1]);
      PSTATE_F := (PSTATE_F | operand[0]);
    }
    case PSTATEField_DAIFClr -> {
      PSTATE_D := (PSTATE_D & NOT'(operand[3]));
      PSTATE_A := (PSTATE_A & NOT'(operand[2]));
      PSTATE_I := (PSTATE_I & NOT'(operand[1]));
      PSTATE_F := (PSTATE_F & NOT'(operand[0]));
    }
  }
}

(* HINT *)
function clause decodeSystem (0b1101010100:[0]:0b00:0b011:0b0010:(bit[4]) CRm:(bit[3]) op2:0b11111) = {
  (SystemHintOp) op := 0; (* ARM: uninitialized *)

  switch CRm:op2 {
    case (0b0000:0b000) -> op := SystemHintOp_NOP
    case (0b0000:0b001) -> op := SystemHintOp_YIELD
    case (0b0000:0b010) -> op := SystemHintOp_WFE
    case (0b0000:0b011) -> op := SystemHintOp_WFI
    case (0b0000:0b100) -> op := SystemHintOp_SEV
    case (0b0000:0b101) -> op := SystemHintOp_SEVL
    case _ -> op := SystemHintOp_NOP
  };

  Some(Hint(op));
}

function clause execute ( Hint(op) ) = {
  switch op {
    case SystemHintOp_YIELD ->
      Hint_Yield()

    case SystemHintOp_WFE -> {
      if EventRegistered() then
        ClearEventRegister()
      else {
        if PSTATE_EL == EL0 then
          AArch64_CheckForWFxTrap(EL1, true);
        if HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL == EL0 | PSTATE_EL == EL1) then
          AArch64_CheckForWFxTrap(EL2, true);
        if HaveEL(EL3) & PSTATE_EL != EL3 then
          AArch64_CheckForWFxTrap(EL3, true);
        WaitForEvent();
      }
    }

    case SystemHintOp_WFI -> {
      if ~(InterruptPending()) then {
        if PSTATE_EL == EL0 then
          AArch64_CheckForWFxTrap(EL1, false);
        if HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL == EL0 | PSTATE_EL == EL1) then
          AArch64_CheckForWFxTrap(EL2, false);
        if HaveEL(EL3) & PSTATE_EL != EL3 then
          AArch64_CheckForWFxTrap(EL3, false);
        WaitForInterrupt();
      };
    }

    case SystemHintOp_SEV ->
      SendEvent()

    case SystemHintOp_SEVL ->
      EventRegisterSet()

    case _ -> () (* do nothing *)
  }
}

(* CLREX *)
function clause decodeSystem (0b1101010100:[0]:0b00:0b011:0b0011:(bit[4]) CRm:0b010:0b11111) = {
  (* ARM: // CRm field is ignored *)
  (uinteger) imm := CRm; (* we need CRm for pretty printing *)
  Some(ClearExclusiveMonitor(imm));
}

function clause execute (ClearExclusiveMonitor(imm)) = {
  ClearExclusiveLocal(ProcessorID());
}

(* DMB opc=0b01*)
(* DSB opc=0b00*)
(* ISB opc=0b10*)
function clause decodeSystem (0b1101010100:[0]:0b00:0b011:0b0011:(bit[4]) CRm:[1]:opc:0b11111) = {
  (* TODO: according to ARM, HCR_EL2.BSU affect the domain, but the pseudo
           code doesn't show any signs of that *)
  (MemBarrierOp) op := 0; (* ARM: uninitialized *)
  (MBReqDomain) domain := 0; (* ARM: uninitialized *)
  (MBReqTypes) types := 0; (* ARM: uninitialized *)

  switch opc {
    case 0b00 -> op := MemBarrierOp_DSB
    case 0b01 -> op := MemBarrierOp_DMB
    case 0b10 -> op := MemBarrierOp_ISB
    case _ -> UnallocatedEncoding()
  };

  switch CRm[3..2] {
    case 0b00 -> domain := MBReqDomain_OuterShareable
    case 0b01 -> domain := MBReqDomain_Nonshareable
    case 0b10 -> domain := MBReqDomain_InnerShareable
    case 0b11 -> domain := MBReqDomain_FullSystem
  };

  switch CRm[1..0] {
    case 0b01 -> types := MBReqTypes_Reads
    case 0b10 -> types := MBReqTypes_Writes
    case 0b11 -> types := MBReqTypes_All
    case _ -> {
      types := MBReqTypes_All;
      domain := MBReqDomain_FullSystem;
    }
  };

  Some(Barrier(op,domain,types));
}

function clause execute ( Barrier(op,domain,types) ) = {
  switch op {
    case MemBarrierOp_DSB ->
      DataSynchronizationBarrier(domain, types)
    case MemBarrierOp_DMB ->
      DataMemoryBarrier(domain, types)
    case MemBarrierOp_ISB ->
      InstructionSynchronizationBarrier()
  };
}

(* SYS L=0b0 *)
(* SYSL L=0b1 *)
function clause decodeSystem (0b1101010100:[L]:0b01:(bit[3]) op1:(bit[4]) CRn:(bit[4]) CRm:(bit[3]) op2:Rt) = {
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: CheckSystemAccess(0b01, op1, CRn, CRm, op2, Rt, L);*)

  (reg_index) t := UInt_reg(Rt);

  (uinteger) sys_op0 := 1;
  (uinteger) sys_op1 := UInt(op1);
  (uinteger) sys_op2 := UInt(op2);
  (uinteger) sys_crn := UInt(CRn);
  (uinteger) sys_crm := UInt(CRm);
  (boolean) has_result := (L == 1);

  Some(System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result));
}

function clause execute ( System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result) ) =
{
  if has_result then
    wX(t) := SysOp_R(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    SysOp_W(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

(* MRS L=1 *)
(* MSR (register) L=0 *)
function clause decodeSystem (0b1101010100:[L]:[1]:[o0]:(bit[3]) op1:(bit[4]) CRn:(bit[4]) CRm:(bit[3]) op2:Rt) = {
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: CheckSystemAccess([0b1]:[o0], op1, CRn, CRm, op2, Rt, L); *)

  (reg_index) t := UInt_reg(Rt);

  (uinteger) sys_op0 := 2 + UInt([o0]);
  (uinteger) sys_op1 := UInt(op1);
  (uinteger) sys_op2 := UInt(op2);
  (uinteger) sys_crn := UInt(CRn);
  (uinteger) sys_crm := UInt(CRm);
  (boolean) read := (L == 1);

  Some(MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read));
}

function clause execute ( MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read) ) = {
  if read then
    wX(t) := System_Get(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    System_Put(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

end decodeSystem

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect pure decodeImplementationDefined
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeImplementationDefined

(* instructions to signal the Sail interpreter that test begins/ends *)
function clause decodeImplementationDefined (0b1101010100:[0]:0b01:0b011:[1]:[_]:0b11:0b0000:0b000:0b0000:[isEnd]) =
{
  Some(ImplementationDefinedTestBeginEnd(isEnd));
}

function clause execute ( ImplementationDefinedTestBeginEnd(isEnd) ) =
{
  if isEnd then
    info("test ends")
  else
    info("test begins");
}

(* instructions to signal ppcmem to stop fetching *)
function clause decodeImplementationDefined (0b1101010100:[0]:0b01:0b011:[1]:[_]:0b11:0b0000:0b000:0b00010) =
{
  Some(ImplementationDefinedStopFetching)
}

function clause execute ( ImplementationDefinedStopFetching ) =
{
  info("stop fetching instructions");
}

(* instructions to signal ppcmem to start a thread *)
function clause decodeImplementationDefined (0b1101010100:[0]:0b01:0b011:[1]:[_]:0b11:0b0000:0b000:0b00011) =
{
  Some(ImplementationDefinedThreadStart)
}

function clause execute ( ImplementationDefinedThreadStart ) =
{
  info("thread start");
}

end decodeImplementationDefined

(* TBNZ *)
(* TBZ *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeTestBranchImmediate ([b5]:0b011011:[op]:(bit[5]) b40:(bit[14]) imm14:Rt) = {
  (reg_index) t := UInt_reg(Rt);

  ([:'R:]) datasize := if b5 == 1 then 64 else 32;
  (uinteger) bit_pos := UInt([b5]:b40);
  (bit) bit_val := op;
  (bit[64]) offset := SignExtend(imm14:0b00);

  Some(TestBitAndBranch(t,datasize,bit_pos,bit_val,offset));
}

function clause execute ( TestBitAndBranch(t,datasize,bit_pos,bit_val,offset) ) = {
  (bit['R]) operand := rX(t);

  if operand[bit_pos] == bit_val then
    BranchTo(rPC() + offset, BranchType_JMP);
}

(* B *)
(* BL *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeUnconditionalBranchImmediate ([op]:0b00101:(bit[26]) imm26) = {
  (BranchType) branch_type := if op == 1 then BranchType_CALL else BranchType_JMP;
  (bit[64]) offset := SignExtend(imm26:0b00);

  Some(BranchImmediate(branch_type,offset));
}

function clause execute (BranchImmediate(branch_type,offset)) = {
  if branch_type == BranchType_CALL then wX(30) := rPC() + 4;

  BranchTo(rPC() + offset, branch_type);
}


val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect {escape} decodeUnconditionalBranchRegister
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeUnconditionalBranchRegister

(* BLR *)
(* BR *)
(* RET *)
function clause decodeUnconditionalBranchRegister (0b1101011:0b00:op:0b11111:0b000000:Rn:0b00000) = {
  (reg_index) n := UInt_reg(Rn);
  (BranchType) branch_type := 0; (* ARM: uninitialized *)

  switch op {
    case 0b00 -> branch_type := BranchType_JMP
    case 0b01 -> branch_type := BranchType_CALL
    case 0b10 -> branch_type := BranchType_RET
    case _ -> UnallocatedEncoding()
  };

  Some(BranchRegister(n,branch_type));
}

function clause execute (BranchRegister(n,branch_type)) =
{
  (bit[64]) target := rX(n);

  if branch_type == BranchType_CALL then wX(30) := rPC() + 4;
  BranchTo(target, branch_type);
}

(* ERET *)
function clause decodeUnconditionalBranchRegister (0b1101011:0b0100:0b11111:0b000000:0b11111:0b00000) =
{
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: if PSTATE_EL == EL0 then UnallocatedEncoding(); *)

  Some(ExceptionReturn);
}

function clause execute (ExceptionReturn) =
{
  AArch64_ExceptionReturn(rELR'(), rSPSR());
}

(* DRPS *)
function clause decodeUnconditionalBranchRegister (0b1101011:0b0101:0b11111:0b000000:0b11111:0b00000) =
{
  (* FIXME: we don't allow register reads in the decoding *)
  (* ARM: if ~(Halted()) | PSTATE_EL == EL0 then UnallocatedEncoding(); *)

  Some(DebugRestorePState);
}

function clause execute (DebugRestorePState) =
{
  DRPSInstruction();
}

end decodeUnconditionalBranchRegister

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeAdvSIMDLoadStoreMultiStruct ((bit[32]) machineCode) =
{
  not_implemented("decodeAdvSIMDLoadStoreMultiStruct");
  Some(Unallocated);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeAdvSIMDLoadStoreMultiStructPostIndexed ((bit[32]) machineCode) =
{
  not_implemented("decodeAdvSIMDLoadStoreMultiStructPostIndexed");
  Some(Unallocated);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeAdvSIMDLoadStoreSingleStruct ((bit[32]) machineCode) =
{
  not_implemented("decodeAdvSIMDLoadStoreSingleStruct");
  Some(Unallocated);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeAdvSIMDLoadStoreSingleStructPostIndexed ((bit[32]) machineCode) =
{
  not_implemented("decodeAdvSIMDLoadStoreSingleStructPostIndexed");
  Some(Unallocated);
}

(* LDR (literal) opc=0b0_ *)
(* LDRSW (literal) opc=0b10 *)
(* PRFM (literal) opc=0b11 *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadRegisterLiteral ((bit[2]) opc:0b011:[0]:0b00:(bit[19]) imm19:Rt) =
{
  (reg_index) t := UInt_reg(Rt);
  (MemOp) memop := MemOp_LOAD;
  (boolean) _signed := false;
  (uinteger) size := 0; (* ARM: uninitialized *)
  (bit[64]) offset := 4; (* ARM: uninitialized *)

  switch opc {
    case 0b00 ->
      size := 4 (* LDR (literal) 32 *)
    case 0b01 ->
      size := 8 (* LDR (literal) 64 *)
    case 0b10 -> { (* LDRSW (literal) *)
      size := 4;
      _signed := true;
    }
    case 0b11 -> (* PRFM (literal) *)
      memop := MemOp_PREFETCH
  };

  offset := SignExtend(imm19:0b00);

  ([:'D:]) datasize := size*8; (* not in ARM ARM *)

  Some(LoadLiteral(t,memop,_signed,size,offset,datasize));
}

function clause execute ( LoadLiteral(t,memop,_signed,size,offset,([:'D:]) datasize) ) = {
  (bit[64]) address := rPC() + offset;
  (bit['D]) data := 0; (* ARM: uninitialized *)

  switch memop {
    case MemOp_LOAD -> {
      data := flush_read_buffer(
        rMem(empty_read_buffer, address, size, AccType_NORMAL),
        size
      );
      if _signed then
        wX(t) := (bit[64]) (SignExtend(data))
      else
        wX(t) := data;
    }
    case MemOp_PREFETCH ->
      Prefetch(address,(bit[5]) t)
  };
}

(* LDAR   size=0b1_,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDARB  size=0b00,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDARH  size=0b01,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDAXP  size=0b1_,o2=0,L=1,o1=1,o0=1,rs=(1)(1)(1)(1)(1)                     *)
(* LDAXR  size=0b1_,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDAXRB size=0b00,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDAXRH size=0b01,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDXP   size=0b1_,o2=0,L=1,o1=1,o0=0,rs=(1)(1)(1)(1)(1)                     *)
(* LDXR   size=0b1_,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDXRB  size=0b00,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* LDXRH  size=0b01,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* STLR   size=0b1_,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* STLRB  size=0b00,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* STLRH  size=0b01,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) *)
(* STLXP  size=0b1_,o2=0,L=0,o1=1,o0=1                                        *)
(* STLXR  size=0b1_,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) *)
(* STLXRB size=0b00,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) *)
(* STLXRH size=0b01,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) *)
(* STXP   size=0b1_,o2=0,L=0,o1=1,o0=0                                        *)
(* STXR   size=0b1_,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) *)
(* STXRB  size=0b00,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) *)
(* STXRH  size=0b01,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreExclusive ((bit[2]) size:0b001000:[o2]:[L]:[o1]:Rs:[o0]:Rt2:Rn:Rt) =
{
  (reg_index) n := UInt_reg(Rn);
  (reg_index) t := UInt_reg(Rt);
  (reg_index) t2 := UInt_reg(Rt2); (* ignored by load/store single register *)
  (reg_index) s := UInt_reg(Rs);   (* ignored by all loads and store-release *)

  if ([o2,o1,o0]) == 0b100 | ([o2,o1] == 0b11) then UnallocatedEncoding();
  if o1 == 1 & size[1] == 0 then UnallocatedEncoding();

  (AccType) acctype := if o0 == 1 then AccType_ORDERED else AccType_ATOMIC;
  (boolean) excl := (o2 == 0);
  (boolean) pair := (o1 == 1);
  (MemOp) memop := if L == 1 then MemOp_LOAD else MemOp_STORE;
  elsize := lsl(8, UInt(size));
  ([:'R:]) regsize := if elsize == 64 then 64 else 32;
  ([:'D:]) datasize := if pair then elsize * 2 else elsize;

  (* lemma: pair --> datasize = 2*regsize *)
  (* follows from "if o1 == 1 & size[1] == 0 then UnallocatedEncoding();" *)

  Some(LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,datasize));
}

function clause execute ( LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,([:'D:]) datasize) ) = {
  (bit[64]) address := 0; (* ARM: uninitialized *)
  (bit['D]) data := 0; (* ARM: uninitialized *)
  (*constant*) (uinteger) dbytes := datasize quot 8;
  (boolean) rt_unknown := false;
  (boolean) rn_unknown := false;

  if memop == MemOp_LOAD & pair & t == t2 then {
    UnallocatedEncoding(); (* ARM:
    (Constraint) c := ConstrainUnpredictable();
    assert( vIN(c, [Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP]) );
    switch c {
      case Constraint_UNKNOWN -> rt_unknown =: true (* result is UNKNOWN *)
      case Constraint_UNDEF ->   UnallocatedEncoding()
      case Constraint_NOP ->     EndOfInstruction()
    };*)
  };

  if memop == MemOp_STORE & excl then {
    if s == t | (pair & s == t2) then {
      UnallocatedEncoding(); (* ARM:
      (Constraint) c := ConstrainUnpredictable();
      assert( vIN(c, [Constraint_UNKNOWN, Constraint_NONE, Constraint_UNDEF, Constraint_NOP]) );
      switch c {
        case Constraint_UNKNOWN -> rt_unknown := true  (* store UNKNOWN value *)
        case Constraint_NONE ->    rt_unknown := false (* store original value *)
        case Constraint_UNDEF ->   UnallocatedEncoding()
        case Constraint_NOP ->     EndOfInstruction()
      };*)
    };
    if s == n & n != 31 then {
      UnallocatedEncoding(); (* ARM:
      (Constraint) c := ConstrainUnpredictable();
      assert( vIN(c, [Constraint_UNKNOWN, Constraint_NONE, Constraint_UNDEF, Constraint_NOP]) );
      switch c {
        case Constraint_UNKNOWN -> rn_unknown := true  (* address is UNKNOWN *)
        case Constraint_NONE ->    rn_unknown := false (* address is original base *)
        case Constraint_UNDEF ->   UnallocatedEncoding()
        case Constraint_NOP ->     EndOfInstruction()
      };*)
    };
  };

  (* this is a hack to allow the result of store-exclusive to be observed
  before anything else *)
  (bit) status := 0;
  if memop == MemOp_STORE & excl then {
    (*(bit)*) status := if speculate_exclusive_success() then 0 else 1;
    wX(s) := (bit[32]) (ZeroExtend([status]));

    (* should be:
    if status == 1 then return ();
    *)
  };
  if status == 1 then () else {

  if n == 31 then {
    CheckSPAlignment();
    address := rSP();
  } else if rn_unknown then
    address := (bit[64]) UNKNOWN
  else
    address := rX(n);

  switch memop {
    case MemOp_STORE -> {
      (* anounce the address *)
      wMem_Addr(address, dbytes, acctype, excl);

      if rt_unknown then
        data := (bit['D]) UNKNOWN
      else if pair then {
        assert( excl, None );
        (bit['R]) el1 := rX(t); (* ARM: bit[datasize / 2] see lemma in the decoding *)
        (bit['R]) el2 := rX(t2); (* ARM: bit[datasize / 2] see lemma in the decoding *)
        data := if BigEndian() then el1:el2 else el2:el1;
      } else
        (bit['D]) data := rX(t);

      if excl then {
        (* store {release} exclusive register|pair (atomic) *)
        (bit) status := 1;
        (* Check whether the Exclusive Monitors are set to include the *)
        (* physical memory locations corresponding to virtual address *)
        (* range [address, address+dbytes-1]. *)
        if AArch64_ExclusiveMonitorsPass(address, dbytes) then {
          (* This atomic write will be rejected if it does not refer *)
          (* to the same physical locations after address translation. *)
          (* ARM: wMem(address, dbytes, acctype) := data;
          status := ExclusiveMonitorsStatus(); *)
          status := flush_write_buffer_exclusive(
            wMem_exclusive(empty_write_buffer, address, dbytes, acctype, data)
          );
        };
        (* ARM: the following code was moved up, see note there
        wX(s) := (bit[32]) (ZeroExtend([status]));
        *)
      } else {
        (* store release register (atomic) *)
        flush_write_buffer(
          wMem(empty_write_buffer, address, dbytes, acctype, data)
        );
      };
    }

    case MemOp_LOAD -> {
      if excl then {
        (* Tell the Exclusive Monitors to record a sequence of one or more atomic *)
        (* memory reads from virtual address range [address, address+dbytes-1]. *)
        (* The Exclusive Monitor will only be set if all the reads are from the *)
        (* same dbytes-aligned physical address, to allow for the possibility of *)
        (* an atomicity break if the translation is changed between reads. *)
        AArch64_SetExclusiveMonitors(address, dbytes);
      };

      if pair then {
        (* load exclusive pair *)
        assert( excl, None );
        if rt_unknown then
          (* ConstrainedUNPREDICTABLE case *)
          wX(t) := (bit['D]) UNKNOWN
        else if elsize == 32 then {
          (* 32-bit load exclusive pair (atomic) *)
          data := flush_read_buffer(
            rMem_exclusive(empty_read_buffer, address, dbytes, acctype),
            dbytes
          );
          if BigEndian() then {
            wX(t) := data[(datasize - 1)..elsize];
            wX(t2) := data[(elsize - 1)..0];
          } else {
            wX(t) := data[(elsize - 1)..0];
            wX(t2) := data[(datasize - 1)..elsize];
          };
        } else { (* elsize == 64 *)
          (* 64-bit load exclusive pair (not atomic), *)
          (* but must be 128-bit aligned *)
          if address != Align(address, dbytes) then {
            (boolean) iswrite := false;
            (boolean) secondstage := false;
            AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
          };
          (read_buffer_type)  read_buffer := rMem_exclusive(empty_read_buffer, address + 0, 8, acctype);
                              read_buffer := rMem_exclusive(read_buffer,       address + 8, 8, acctype);
          (bit[128]) value := flush_read_buffer(read_buffer, 8*2);
          wX(t) := value[63..0];
          wX(t2) := value[127..64];
        };
      } else {
        (* load {acquire} {exclusive} single register *)
        data := flush_read_buffer(
          rMem'(empty_read_buffer, address, dbytes, acctype, excl),
          dbytes
        );
        wX(t) := (bit['R]) (ZeroExtend(data));
      };
    }
  };
  };
}

(* LDNP *)
(* STNP *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreNoAllocatePairOffset ((bit[2]) opc:0b101:[0]:0b000:[L]:(bit[7]) imm7:Rt2:Rn:Rt) =
{
  (boolean) wback := false;
  (boolean) postindex := false;

  (* Shared decode *)

  (reg_index) n := UInt_reg(Rn);
  (reg_index) t := UInt_reg(Rt);
  (reg_index) t2 := UInt_reg(Rt2);
  (AccType) acctype := AccType_STREAM;
  (MemOp) memop := if L == 1 then MemOp_LOAD else MemOp_STORE;
  if opc[0] == 1 then UnallocatedEncoding();
  (uinteger) scale := 2 + UInt([opc[1]]);
  ([:'D:]) datasize := lsl(8, scale);
  (bit[64]) offset := LSL(SignExtend(imm7), scale);

  Some(LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,datasize,offset));
}

function clause execute ( LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,([:'D:]) datasize,offset) ) = {
  (bit[64]) address := 0; (* ARM: uninitialized *)
  (bit['D]) data1 := 0; (* ARM: uninitialized *)
  (bit['D]) data2 := 0; (* ARM: uninitialized *)
  (*constant*) (uinteger) dbytes := datasize quot 8;
  (boolean) rt_unknown := false;

  if memop == MemOp_LOAD & t == t2 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c = ConstrainUnpredictable();
    assert c IN {Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP};

    case c of
      when Constraint_UNKNOWN rt_unknown = TRUE; // result is UNKNOWN
      when Constraint_UNDEF   UnallocatedEncoding();
      when Constraint_NOP     EndOfInstruction();
    };*)
  };

  if n == 31 then {
    CheckSPAlignment();
    address := rSP();
  } else
    address := rX(n);

  if ~(postindex) then
    address := address + offset;

  if memop == MemOp_STORE then
    (* anounce the address *)
    wMem_Addr(address, dbytes * 2, acctype, false);

  (* this is a hack to allow the address write back to be observed
     before the memory access *)
  if wback then {
    let address' = (bit[64]) (if ~(postindex) then address else (address + offset)) in
    if n == 31 then
      wSP() := address'
    else
      wX(n) := address'
  };

  switch memop {
    case MemOp_STORE -> {
      if rt_unknown & t == n then
        data1 := (bit['D]) UNKNOWN
      else
        data1 := rX(t);
      if rt_unknown & t2 == n then
        data2 := (bit['D]) UNKNOWN
      else
        data2 := rX(t2);

      (write_buffer_type) write_buffer := wMem(empty_write_buffer, address + 0,      dbytes, acctype, data1);
                          write_buffer := wMem(write_buffer,       address + dbytes, dbytes, acctype, data2);
      flush_write_buffer(write_buffer);
    }

    case MemOp_LOAD -> {
      (read_buffer_type)  read_buffer := rMem(empty_read_buffer, address + 0     , dbytes, acctype);
                          read_buffer := rMem(read_buffer,       address + dbytes, dbytes, acctype);
      (bit['D*2]) read_data := flush_read_buffer(read_buffer, dbytes*2);
      data1 := read_data[(datasize - 1)..0];
      data2 := read_data[((datasize * 2) - 1)..datasize];

      if rt_unknown then {
        data1 := (bit['D]) UNKNOWN;
        data2 := (bit['D]) UNKNOWN;
      };
      wX(t) := data1;
      wX(t2) := data2;
    }
  };

(* ARM: the following code was moved up, see note there
  if wback then {
    if postindex then
      address := address + offset;
    if n == 31 then
      wSP() := address
    else
      wX(n) := address;
  };
*)
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> sharedDecodeLoadImmediate((bit[2]) opc,(bit[2]) size,Rn,Rt,wback,postindex,(uinteger) scale,offset,acctype,(bool) prefetchAllowed) =
{
  (reg_index) n := UInt_reg(Rn);
  (reg_index) t := UInt_reg(Rt);
  (* ARM: inorder to unify the decoding acctype was moved out.
          AccType_UNPRIV for LDT*/STT* and AccType_NORMAL for the rest.
  (AccType) acctype := AccType_NORMAL/AccType_UNPRIV; *)
  (MemOp) memop := 0; (* ARM: uninitialized *)
  (boolean) _signed := false; (* ARM: uninitialized *)
  ([:'R:]) regsize := 64; (* ARM: uninitialized *)

  if opc[1] == 0 then {
    (* store or zero-extending load *)
    memop := if opc[0] == 1 then MemOp_LOAD else MemOp_STORE;
    regsize := if size == 0b11 then 64 else 32;
    _signed := false;
  } else {
    if size == 0b11 then {
      (* ARM: we use the following if/else to unify the decoding *)
      if prefetchAllowed then {
        memop := MemOp_PREFETCH;
        if opc[0] == 1 then UnallocatedEncoding();
      } else {
        (* no unprivileged prefetch *)
        UnallocatedEncoding();
      };
    } else {
      (* sign-extending load *)
      memop := MemOp_LOAD;
      if size == 0b10 & opc[0] == 1 then UnallocatedEncoding();
      regsize := if opc[0] == 1 then 32 else 64;
      _signed := true;
    };
  };

  ([:'D:]) datasize := lsl(8, scale);

  Some(LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize));
}

(* LDR/STR (immediate) post-index *)
(* LDRB/STRB (immediate) post-index *)
(* LDRH/STRH (immediate) post-index *)
(* LDRSB (immediate) post-index *)
(* LDRSH (immediate) post-index *)
(* LDRSW (immediate) post-index *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterImmediatePostIndexed (size:0b111:[0]:0b00:opc:[0]:(bit[9]) imm9:0b01:Rn:Rt) = {
  (boolean) wback := true;
  (boolean) postindex := true;
  (uinteger) scale := UInt(size);
  (bit[64]) offset := SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

function clause execute ( LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,([:'D:]) datasize) ) = {
  (bit[64]) address := 0; (* ARM: uninitialized *)
  (bit['D]) data := 0; (* ARM: uninitialized *)
  (boolean) wb_unknown := false;
  (boolean) rt_unknown := false;

  if memop == MemOp_LOAD & wback & n == t & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_WBSUPPRESS -> wback := false     (* writeback is suppressed *)
      case Constraint_UNKNOWN ->    wb_unknown := true (* writeback is UNKNOWN *)
        case Constraint_UNDEF ->      UnallocatedEncoding()
        case Constraint_NOP ->        EndOfInstruction()
    };*)
  };

  if memop == MemOp_STORE & wback & n == t & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_NONE ->    rt_unknown := false (* value stored is original value *)
      case Constraint_UNKNOWN -> rt_unknown := true  (* value stored is UNKNOWN *)
        case Constraint_UNDEF ->   UnallocatedEncoding()
        case Constraint_NOP ->     EndOfInstruction()
    };*)
  };

  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment();
    address := rSP();
  } else
    address := rX(n);

  if ~(postindex) then
    address := address + offset;

  if memop == MemOp_STORE then
    (* anounce the address *)
    wMem_Addr(address, datasize quot 8, acctype, false);

  (* this is a hack to allow the address write back to be observed
     before the memory access *)
  if wback then {
    let address' = (bit[64]) (if ~(postindex) then address else (address + offset)) in
    if n == 31 then
      wSP() := address'
    else
      wX(n) := address'
  };

  switch memop {
    case MemOp_STORE -> {
      if rt_unknown then
        data := (bit['D]) UNKNOWN
      else
        data := rX(t);

      flush_write_buffer(
        wMem(empty_write_buffer, address, datasize quot 8, acctype, data)
      );
    }

    case MemOp_LOAD -> {
      data := flush_read_buffer(
        rMem(empty_read_buffer, address, datasize quot 8, acctype),
        datasize quot 8
      );
      if _signed then
        wX(t) := (bit['R]) (SignExtend(data)) (* ARM: regsize *)
      else
        wX(t) := (bit['R]) (ZeroExtend(data)); (* ARM: regsize *)
    }

    case MemOp_PREFETCH ->
      Prefetch(address,(bit[5]) t)
  };

(* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address := (bit[64]) UNKNOWN
    else if postindex then
      address := address + offset;
    if n == 31 then
      wSP() := address
    else
      wX(n) := address;
  };
*)
}

(* LDR/STR (immediate) pre-index *)
(* LDRB/STRB (immediate) pre-index *)
(* LDRH/STRH (immediate) pre-index *)
(* LDRSB (immediate) pre-index *)
(* LDRSH (immediate) pre-index *)
(* LDRSW (immediate) pre-index *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterImmediatePreIndexed (size:0b111:[0]:0b00:opc:[0]:(bit[9]) imm9:0b11:Rn:Rt) =
{
  (boolean) wback := true;
  (boolean) postindex := false;
  (uinteger) scale := UInt(size);
  (bit[64]) offset := SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}. option<(ast<'R,'D>)> sharedDecodeLoadRegister(Rn,Rt,Rm,(bit[2]) opc,(bit[2]) size,wback,postindex,(uinteger) scale,extend_type,shift) = {
  (reg_index) n := UInt_reg(Rn);
  (reg_index) t := UInt_reg(Rt);
  (reg_index) m := UInt_reg(Rm);
  (AccType) acctype := AccType_NORMAL;
  (MemOp) memop := 0; (* ARM: uninitialized *)
  (boolean) _signed := 0; (* ARM: uninitialized *)
  ([:'R:]) regsize := 64; (* ARM: uninitialized *)

  if opc[1] == 0 then {
    (* store or zero-extending load *)
    memop := if opc[0] == 1 then MemOp_LOAD else MemOp_STORE;
    regsize := if size == 0b11 then 64 else 32;
    _signed := false;
  } else {
    if size == 0b11 then {
      memop := MemOp_PREFETCH;
      if opc[0] == 1 then UnallocatedEncoding();
    } else {
      (* sign-extending load *)
      memop := MemOp_LOAD;
      if size == 0b10 & opc[0] == 1 then UnallocatedEncoding();
      regsize := if opc[0] == 1 then 32 else 64;
      _signed := true;
    };
  };

  ([:'D:]) datasize := lsl(8, scale);

  Some(LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize));
}

(* LDR/STR (register) *)
(* LDRB/STRB (register) *)
(* LDRH/STRH (register) *)
(* LDRSB (register) *)
(* LDRSH (register) *)
(* LDRSW (register) *)
(* PRFM (register) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterRegisterOffset (size:0b111:[0]:0b00:opc:[1]:Rm:option_v:[S]:0b10:Rn:Rt) =
{
  (boolean) wback := false;
  (boolean) postindex := false;
  (uinteger) scale := UInt(size);
  if option_v[1] == 0 then UnallocatedEncoding(); (* sub-word index *)
  (ExtendType) extend_type := DecodeRegExtend(option_v);
  (uinteger) shift := if S == 1 then scale else 0;

  sharedDecodeLoadRegister(Rn,Rt,Rm,opc,size,wback,postindex,scale,extend_type,shift);
}

function clause execute ( LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,([:'D:]) datasize) ) = {
  (bit[64]) offset := ExtendReg(m, extend_type, shift);
  (bit[64]) address := 0; (* ARM: uninitialized *)
  (bit['D]) data := 0; (* ARM: uninitialized *)
  (boolean) wb_unknown := false;
  (boolean) rt_unknown := false;

  if memop == MemOp_LOAD & wback & n == t & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_WBSUPPRESS -> wback := false     (* writeback is suppressed *)
      case Constraint_UNKNOWN ->    wb_unknown := true (* writeback is UNKNOWN *)
      case Constraint_UNDEF ->      UnallocatedEncoding()
      case Constraint_NOP ->        EndOfInstruction()
    };*)
  };

  if memop == MemOp_STORE & wback & n == t & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_NONE ->    rt_unknown := false (* value stored is original value *)
      case Constraint_UNKNOWN -> rt_unknown := true  (* value stored is UNKNOWN *)
      case Constraint_UNDEF ->   UnallocatedEncoding()
      case Constraint_NOP ->     EndOfInstruction()
    };*)
  };

  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment();
    address := rSP();
  } else
    address := rX(n);

  if ~(postindex) then
    address := address + offset;

  if memop == MemOp_STORE then
    (* anounce the address *)
    wMem_Addr(address, datasize quot 8, acctype, false);

  (* this is a hack to allow the address write back to be observed
     before the memory access *)
  if wback then {
    let address' = (bit[64]) (if ~(postindex) then address else (address + offset)) in
    if n == 31 then
      wSP() := address'
    else
      wX(n) := address'
  };

  switch memop {
    case MemOp_STORE -> {
      if rt_unknown then
        data := (bit['D]) UNKNOWN
      else
        data := rX(t);

      flush_write_buffer(
        wMem(empty_write_buffer, address, datasize quot 8, acctype, data)
      );
    }

    case MemOp_LOAD -> {
      data := flush_read_buffer(
        rMem(empty_read_buffer, address, datasize quot 8, acctype),
        datasize quot 8
      );
      if _signed then
        wX(t) := (bit['R]) (SignExtend(data))
      else
        wX(t) := (bit['R]) (ZeroExtend(data));
    }

    case MemOp_PREFETCH ->
      Prefetch(address,(bit[5]) t)
  };

(* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address := (bit[64]) UNKNOWN
    else if postindex then
      address := address + offset;
    if n == 31 then
      wSP() := address
    else
      wX(n) := address;
  };
*)
}

(* LDTR/STTR *)
(* LDTRB/STTRB *)
(* LDTRH/STTRH *)
(* LDTRSB *)
(* LDTRSH *)
(* LDTRSW *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterUnprivileged (size:0b111:[0]:0b00:opc:[0]:(bit[9]) imm9:0b10:Rn:Rt) =
{
  (boolean) wback := false;
  (boolean) postindex := false;
  (uinteger) scale := UInt(size);
  (bit[64]) offset := SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_UNPRIV,false);
}

(* LDUR/STRUR *)
(* LDURB/STURB *)
(* LDURH/STURH *)
(* LDURSB *)
(* LDURSH *)
(* LDURSW *)
(* PRFUM *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterUnscaledImmediate (size:0b111:[0]:0b00:opc:[0]:(bit[9]) imm9:0b00:Rn:Rt) = {
  (boolean) wback := false;
  (boolean) postindex := false;
  (uinteger) scale := UInt(size);
  (bit[64]) offset := SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,true);
}

(* LDR/STR (immediate) Unsigned offset *)
(* LDRB/STRB (immediate) Unsigned offset *)
(* LDRH/STRH (immediate) Unsigned offset *)
(* LDRSB (immediate) Unsigned offset *)
(* LDRSH (immediate) Unsigned offset *)
(* LDRSW (immediate) Unsigned offset *)
(* PRFM (immediate) Unsigned offset *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterUnsignedImmediate (size:0b111:[0]:0b01:opc:(bit[12]) imm12:Rn:Rt) =
{
  (boolean) wback := false;
  (boolean) postindex := false;
  (uinteger) scale := UInt(size);
  (bit[64]) offset := LSL(ZeroExtend(imm12), scale);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,true);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> sharedDecodeLoadStorePair(L,(bit[2]) opc,imm7,Rn,Rt,Rt2,wback,postindex) =
{
  (reg_index) n := UInt_reg(Rn);
  (reg_index) t := UInt_reg(Rt);
  (reg_index) t2 := UInt_reg(Rt2);
  (AccType) acctype := AccType_NORMAL;
  (MemOp) memop := if L == 1 then MemOp_LOAD else MemOp_STORE;
  if [L,opc[0]] == 0b01 | opc == 0b11 then UnallocatedEncoding();
  (boolean) _signed := (opc[0] != 0);
  (uinteger) scale := 2 + UInt([opc[1]]);
  ([:'D:]) datasize := lsl(8, scale);
  (bit[64]) offset := LSL(SignExtend(imm7), scale);

  Some(LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize,offset));
}

(* LDP signed offset *)
(* LDPSW signed offset *)
(* STP signed offset *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterPairOffset (opc:0b101:[0]:0b010:[L]:(bit[7]) imm7:Rt2:Rn:Rt) =
{
  (boolean) wback := false;
  (boolean) postindex := false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

function clause execute ( LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,([:'D:])datasize,offset) ) = {
  (bit[64]) address := 0; (* ARM: uninitialized *)
  (bit['D]) data1 := 0; (* ARM: uninitialized *)
  (bit['D]) data2 := 0; (* ARM: uninitialized *)
  (*constant*) (uinteger) dbytes := datasize quot 8;
  (boolean) rt_unknown := false;
  (boolean) wb_unknown := false;

  if memop == MemOp_LOAD & wback & (t == n | t2 == n) & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_WBSUPPRESS -> wback := false     (* writeback is suppressed *)
      case Constraint_UNKNOWN ->    wb_unknown := true (* writeback is UNKNOWN *)
        case Constraint_UNDEF ->      UnallocatedEncoding()
        case Constraint_NOP ->        EndOfInstruction()
    };*)
  };

  if memop == MemOp_STORE & wback & (t == n | t2 == n) & n != 31 then {
    UnallocatedEncoding(); (* ARM:
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_NONE ->    rt_unknown := false (* value stored is pre-writeback *)
      case Constraint_UNKNOWN -> rt_unknown := true  (* value stored is UNKNOWN *)
        case Constraint_UNDEF ->   UnallocatedEncoding()
        case Constraint_NOP ->     EndOfInstruction()
    };*)
  };

  if memop == MemOp_LOAD & t == t2 then {
    UnallocatedEncoding(); (* ARM
    Constraint c := ConstrainUnpredictable();
    assert( c vIN [Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      case Constraint_UNKNOWN -> rt_unknown := true (* result is UNKNOWN *)
      case Constraint_UNDEF ->   UnallocatedEncoding()
      case Constraint_NOP ->     EndOfInstruction()
    };*)
  };

  if n == 31 then {
    CheckSPAlignment();
    address := rSP();
  } else
    address := rX(n);

  if ~(postindex) then
    address := address + offset;

  if memop == MemOp_STORE then
    (* anounce the address *)
    wMem_Addr(address, dbytes * 2, acctype, false);

  (* this is a hack to allow the address write back to be observed
     before the memory access *)
  if wback then {
    let address' = (bit[64]) (if ~(postindex) then address else (address + offset)) in
    if n == 31 then
      wSP() := address'
    else
      wX(n) := address'
  };

  switch memop {
    case MemOp_STORE -> {
      if rt_unknown & t == n then
        data1 := (bit['D]) UNKNOWN
      else
        data1 := rX(t);
      if rt_unknown & t2 == n then
        data2 := (bit['D]) UNKNOWN
      else
        data2 := rX(t2);

      (write_buffer_type) write_buffer := wMem(empty_write_buffer, address + 0,      dbytes, acctype, data1);
                          write_buffer := wMem(write_buffer,       address + dbytes, dbytes, acctype, data2);
      flush_write_buffer(write_buffer);
    }

    case MemOp_LOAD -> {
      (read_buffer_type)  read_buffer := rMem(empty_read_buffer, address + 0, dbytes, acctype);
                          read_buffer := rMem(read_buffer,       address + dbytes, dbytes, acctype);
      (bit['D*2]) read_data := flush_read_buffer(read_buffer, dbytes*2);
      data1 := read_data[(datasize - 1) .. 0];
      data2 := read_data[((datasize * 2) - 1) .. datasize];
      if rt_unknown then {
        data1 := (bit['D]) UNKNOWN;
        data2 := (bit['D]) UNKNOWN;
      };
      if _signed then {
        wX(t)  := (bit[64]) (SignExtend(data1));
        wX(t2) := (bit[64]) (SignExtend(data2));
      } else {
        wX(t)  := data1;
        wX(t2) := data2;
      };
    }
  };

(* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address := (bit[64]) UNKNOWN
    else if postindex then
      address := address + offset;
    if n == 31 then
      wSP() := address
    else
      wX(n) := address;
  };
*)
}

(* LDP post-index *)
(* LDPSW post-index *)
(* STP post-index *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterPairPostIndexed (opc:0b101:[0]:0b001:[L]:(bit[7]) imm7:Rt2:Rn:Rt) =
{
  (boolean) wback := true;
  (boolean) postindex := true;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

(* LDP pre-index *)
(* LDPSW pre-index *)
(* STP pre-index *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadStoreRegisterPairPreIndexed (opc:0b101:[0]:0b011:[L]:(bit[7]) imm7:Rt2:Rn:Rt) =
{
  (boolean) wback := true;
  (boolean) postindex := false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

(* ADD/ADDS (immediate) *)
(* SUB/SUBS (immediate) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeAddSubtractImmediate ([sf]:[op]:[S]:0b10001:shift:(bit[12]) imm12:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op == 1);
  (boolean) setflags := (S == 1);
  (bit['R]) imm := 0; (* ARM: uninitialized *)

  switch shift {
    case 0b00 -> imm := ZeroExtend(imm12)
    case 0b01 -> imm := ZeroExtend(imm12 : (0b0 ^^ 12))
    case [1,_] -> ReservedValue()
  };

  Some(AddSubImmediate(d,n,datasize,sub_op,setflags,imm));
}

function clause execute (AddSubImmediate(d,n,datasize,sub_op,setflags,imm)) = {
  (bit['R]) operand1 := if n == 31 then rSP() else rX(n);
  (bit['R]) operand2 := imm;
  (bit) carry_in := 0; (* ARM: uninitialized *)

  if sub_op then {
    operand2 := NOT(operand2);
    carry_in := 1;
  }
  else
    carry_in := 0;

  let (result,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {

    if setflags then
      wPSTATE_NZCV() := nzcv;

    if (d == 31 & ~(setflags)) then
      wSP() := result
    else
      wX(d) := result;
  }
}

(* BFM *) 
(* SBFM *)
(* UBFM *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeBitfield ([sf]:opc:0b100110:[N]:(bit[6]) immr:(bit[6]) imms:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;

  (boolean) inzero := false; (* ARM: uninitialized *)
  (boolean) extend := false; (* ARM: uninitialized *)
  (uinteger) R := 0; (* ARM: uninitialized *)
  (uinteger) S := 0; (* ARM: uninitialized *)

  switch opc {
    case 0b00 -> {inzero := true; extend := true}   (* SBFM *)
    case 0b01 -> {inzero := false; extend := false} (* BFM *)
    case 0b10 -> {inzero := true; extend := false}  (* UBFM *)
    case 0b11 -> UnallocatedEncoding()
  };

  if sf == 1 & N != 1 then ReservedValue();
  if sf == 0 & (N != 0 | immr[5] != 0 | imms[5] != 0) then ReservedValue();

  R := UInt(immr);
  S := UInt(imms);

  let ((bit['R]) wmask, (bit['R]) tmask) = (DecodeBitMasks(N, imms, immr, false)) in {

  Some(BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask));
}}


function clause execute (BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask)) = {
  (bit['R]) dst := if inzero then Zeros() else rX(d);
  (bit['R]) src := rX(n);

  (* preform bitfield move on low bits *)
  (bit['R]) bot := ((dst & NOT(wmask)) | (ROR(src, R) & wmask));

  (* determine extension bits (sign, zero or dest register) *)
  (bit['R]) top := if extend then Replicate([src[S]]) else dst;

  (* combine extension bits and result bits *)
  wX(d) := ((top & NOT(tmask)) | (bot & tmask));
}

(* EXTR *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeExtract ([sf]:0b00:0b100111:[N]:0b0:Rm:(bit[6]) imms:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (uinteger) lsb := 0; (* ARM: uninitialized *)

  if N != sf then UnallocatedEncoding();
  if sf == 0 & imms[5] == 1 then ReservedValue();
  lsb := UInt(imms);

  Some(ExtractRegister(d,n,m,datasize,lsb));
}

function clause execute ( ExtractRegister(d,n,m,([:'R:]) datasize,lsb) ) = {
  (bit['R]) result := 0; (* ARM: uninitialized *)
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);

  (bit[2*'R]) concat := operand1:operand2;
  result := concat[(lsb + datasize - 1)..lsb];
  wX(d) := result;
}

(* AND/ANDS (immediate) *)
(* EOR (immediate) *)
(* ORR (immediate) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLogicalImmediate ([sf]:opc:0b100100:[N]:(bit[6]) immr:(bit[6]) imms:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) setflags := false; (* ARM: uninitialized *)
  (LogicalOp) op := LogicalOp_AND; (* ARM: uninitialized *)
  switch opc {
    case 0b00 -> {op := LogicalOp_AND; setflags := false}
    case 0b01 -> {op := LogicalOp_ORR; setflags := false}
    case 0b10 -> {op := LogicalOp_EOR; setflags := false}
    case 0b11 -> {op := LogicalOp_AND; setflags := true}
  };

  if sf == 0 & N != 0 then ReservedValue();
  let (imm,_) = (DecodeBitMasks(N, imms, immr, true)) in {

  Some(LogicalImmediate(d,n,datasize,setflags,op,imm));
}}

function clause execute (LogicalImmediate(d,n,([:'R:]) datasize,setflags,op,imm)) = {
  (bit['R]) result := 0; (* ARM: uninitialized *)
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := imm;

  switch op {
    case LogicalOp_AND -> result := (operand1 & operand2)
    case LogicalOp_ORR -> result := (operand1 | operand2)
    case LogicalOp_EOR -> result := (operand1 ^ operand2)
  };

  if setflags then
    wPSTATE_NZCV() := ([result[length(result) - 1]]:[IsZeroBit(result)]:0b00);

  if d == 31 & ~(setflags) then
    wSP() := result
  else
    wX(d) := result;
}

(* MOVK *)
(* MOVN *)
(* MOVZ *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeMoveWideImmediate ([sf]:opc:0b100101:(bit[2]) hw:(bit[16]) imm16:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (bit[16]) imm := imm16;
  (uinteger) pos := 0; (* ARM: uninitialized *)
  (MoveWideOp) opcode := 0; (* ARM: uninitialized *)

  switch opc {
    case 0b00 -> opcode := MoveWideOp_N
    case 0b10 -> opcode := MoveWideOp_Z
    case 0b11 -> opcode := MoveWideOp_K
    case _ -> UnallocatedEncoding()
  };

  if sf == 0 & hw[1] == 1 then UnallocatedEncoding();
  pos := UInt(hw:0b0000);

  Some(MoveWide(d,datasize,imm,pos,opcode));
}

function clause execute ( MoveWide(d,datasize,imm,pos,opcode) ) = {
  (bit['R]) result := 0; (* ARM: uninitialized *)

  if opcode == MoveWideOp_K then
    result := rX(d)
  else
    result := Zeros();

  result[(pos+15)..pos] := imm;
  if opcode == MoveWideOp_N then
    result := NOT(result);
  wX(d) := result;
}

(* ADR *)
(* ADRP *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodePCRelAddressing ([op]:(bit[2]) immlo:0b10000:(bit[19]) immhi:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (boolean) page := (op == 1);
  (bit[64]) imm := 0; (* ARM: uninitialized *)

  if page then
    imm := SignExtend(immhi:immlo:(0b0 ^^ 12))
  else
    imm := SignExtend(immhi:immlo);

  Some(Address(d,page,imm))
}

function clause execute (Address(d,page,imm)) = {
  (bit[64]) base := rPC();

  if page then
    base[11..0] := (bit[12]) (Zeros());

  wX(d) := base + imm;
}

(* ADD/ADDS (extended register) *)
(* SUB/SUBS (extended register) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeAddSubtractExtendedRegister ([sf]:[op]:[S]:0b01011:0b00:0b1:Rm:option_v:(bit[3]) imm3:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op == 1);
  (boolean) setflags := (S == 1);
  (ExtendType) extend_type := DecodeRegExtend(option_v);
  ([|7|]) shift := UInt(imm3);
  if shift > 4 then ReservedValue();

  Some(AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift));
}

function clause execute (AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift)) = {
  (bit['R]) operand1 := if n == 31 then rSP() else rX(n);
  (bit['R]) operand2 := ExtendReg(m, extend_type, shift);
  (bit) carry_in := 0; (* ARM: uninitialized *)

  if sub_op then {
    operand2 := NOT(operand2);
    carry_in := 1;
  } else
    carry_in := 0;

  let (result,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {

    if setflags then
      wPSTATE_NZCV() := nzcv;

    if (d == 31 & ~(setflags)) then
      wSP() := result
    else
      wX(d) := result;
  }
}

(* ADD/ADDS (shifted register) *)
(* SUB/SUBS (shifted register) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeAddSubtractShiftedRegister ([sf]:[op]:[S]:0b01011:shift:0b0:Rm:(bit[6]) imm6:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op == 1);
  (boolean) setflags := (S == 1);

  if shift == 0b11 then ReservedValue();
  if sf == 0 & imm6[5] == 1 then ReservedValue();

  (ShiftType) shift_type := DecodeShift(shift);
  ([|63|]) shift_amount := UInt(imm6);

  Some(AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount));
}

function clause execute (AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount)) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := ShiftReg(m, shift_type, shift_amount);
  (bit) carry_in := 0; (* ARM: uninitialized *)

  if sub_op then {
    operand2 := NOT(operand2);
    carry_in := 1;
  }
  else
    carry_in := 0;

  let (result,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {

    if setflags then
      wPSTATE_NZCV() := nzcv;

    wX(d) := result;
  }
}

(* ADC/ADCS *)
(* SBC/SBCS *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeAddSubtractWithCarry ([sf]:[op]:[S]:0b11010000:Rm:0b000000:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op == 1);
  (boolean) setflags := (S == 1);

  Some(AddSubCarry(d,n,m,datasize,sub_op,setflags));
}

function clause execute( AddSubCarry(d,n,m,datasize,sub_op,setflags)) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);

  if sub_op then
    operand2 := NOT(operand2);

  let (result,nzcv) = (AddWithCarry(operand1, operand2, PSTATE_C)) in {

  if setflags then
    wPSTATE_NZCV() := nzcv;

  wX(d) := result;
}}

(* CCMN (immediate) *)
(* CCMP (immediate) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeConditionalCompareImmediate ((bit[32]) ([sf]:[op]:[1]:0b11010010:(bit[5]) imm5:_cond:[1]:[0]:Rn:[0]:nzcv)) =
{
  (reg_index) n := UInt_reg(Rn);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op ==1);
  (bit[4]) condition := _cond;
  (bit[4]) flags := nzcv;
  (bit['R]) imm := ZeroExtend(imm5);

  Some(ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm));
}

function clause execute (ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm)) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := imm;
  (bit) carry_in := 0;

  (bit[4]) flags' := flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 := NOT(operand2);
      carry_in := 1;
    };
    let (_,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {flags' := nzcv};
  };
  wPSTATE_NZCV() := flags';
}

(* CCMN (register) *)
(* CCMP (register) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeConditionalCompareRegister ((bit[32]) ([sf]:[op]:[1]:0b11010010:Rm:_cond:[0]:[0]:Rn:[0]:nzcv)) = {
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) sub_op := (op ==1);
  (bit[4]) condition := _cond;
  (bit[4]) flags := nzcv;

  Some(ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags));
}

function clause execute (ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags)) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);
  (bit) carry_in := 0;

  (bit[4]) flags' := flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 := NOT(operand2);
      carry_in := 1;
    };
    let (_,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {flags' := nzcv};
  };
  wPSTATE_NZCV() := flags';
}

(* CSEL op=0,o2=0 *)
(* CSINC op=0,o2=1 *)
(* CSINV op=1,o2=0 *)
(* CSNEG op=1,o2=1 *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeConditionalSelect ((bit[32]) ([sf]:[op]:[0]:0b11010100:Rm:_cond:[0]:[o2]:Rn:Rd)) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (bit[4]) condition := _cond;
  (boolean) else_inv := (op == 1);
  (boolean) else_inc := (o2 == 1);

  Some(ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc));
}

function clause execute ( ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc) ) = {
  (bit['R]) result := 0; (* ARM: uninitialized *)
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);

  if ConditionHolds(condition) then
    result := operand1
  else {
    result := operand2;
    if else_inv then result := NOT(result);
    if else_inc then result := result + 1;
  };

  wX(d) := result;
}

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect {escape} decodeData1Source
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeData1Source

(* RBIT *)
(* REV *)
(* REV16 *)
(* REV32 *)
function clause decodeData1Source ([sf]:[1]:[0]:0b11010110:0b00000:0b0000:opc:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);

  ([:'R:]) datasize := if sf == 1 then 64 else 32;

  (RevOp) op := 0; (* ARM: uninitialized *)
  switch opc {
    case 0b00 ->
      op := RevOp_RBIT
    case 0b01 ->
      op := RevOp_REV16
    case 0b10 ->
      op := RevOp_REV32
    case 0b11 -> {
      if sf == 0 then UnallocatedEncoding();
      op := RevOp_REV64;
    }
  };

  Some(Reverse(d,n,datasize,op));
}

function clause execute ( Reverse(d,n,datasize,op) ) = {
  (bit['R]) result := 0; (* ARM uninitialized *)
  (bit[6]) V := 0; (* ARM uninitialized *)

  switch op {
    case RevOp_REV16 -> V := 0b001000
    case RevOp_REV32 -> V := 0b011000
    case RevOp_REV64 -> V := 0b111000
    case RevOp_RBIT ->  V := if datasize == 64 then 0b111111 else 0b011111
  };

  result := rX(n);

  foreach (vbit from 0 to 5) {
    (* Swap pairs of 2^vbit bits in result *)
    if V[vbit] == 1 then {
      (bit['R]) tmp := result;
      (uinteger) vsize := lsl(1, vbit);
      foreach (base from 0 to (datasize - 1) by (2 * vsize)) { (* ARM: while base < datasize do *)
        result[((base+vsize) - 1)..base] := tmp[(base+(2*vsize) - 1)..(base+vsize)];
        result[(base+(2*vsize) - 1)..(base+vsize)] := tmp[(base+vsize - 1)..base];
        (* ARM: base := base + (2 * vsize); *)
      };
    };
  };
  wX(d) := result;
}

(* CLS *)
(* CLZ *)
function clause decodeData1Source ([sf]:[1]:[0]:0b11010110:0b00000:0b00010:[op]:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (CountOp) opcode := if op == 0 then CountOp_CLZ else CountOp_CLS;

  Some(CountLeading(d,n,datasize,opcode));
}

function clause execute (CountLeading(d,n,datasize,opcode)) = {
  (uinteger) result := 0; (* ARM: uninitialized *)
  (bit['R]) operand1 := rX(n);

  if opcode == CountOp_CLZ then
    result := CountLeadingZeroBits(operand1)
  else
    result := CountLeadingSignBits(operand1);

  wX(d) := (bit['R]) result;
}

end decodeData1Source

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect {escape} decodeData2Source
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeData2Source

(* SDIV o1=1 *)
(* UDIV o1=0 *)
function clause decodeData2Source ([sf]:[0]:[0]:0b11010110:Rm:0b00001:[o1]:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) _unsigned := (o1 == 0);

  Some(Division(d,n,m,datasize,_unsigned));
}

function clause execute ( Division(d,n,m,datasize,_unsigned) ) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);
  (integer) result := 0; (* ARM: uninitialized *)

  if IsZero(operand2) then
    result := 0
  else
    result := (* ARM: RoundTowardsZero*) (Int(operand1, _unsigned) quot Int(operand2, _unsigned)); (* FIXME: does quot round towards zero? *)

  wX(d) := (bit['R]) result ; (* ARM: result[(datasize-1)..0] *)
}

(* ASRV *)
(* LSLV *)
(* LSRV *)
(* RORV *)
function clause decodeData2Source ([sf]:[0]:[0]:0b11010110:Rm:0b0010:op2:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (ShiftType) shift_type := DecodeShift(op2);

  Some(Shift(d,n,m,datasize,shift_type));
}

function clause execute (Shift(d,n,m,datasize,shift_type)) = {
  (bit['R]) result := 0; (* ARM: uninitialized *)
  (bit['R]) operand2 := rX(m);

  result := ShiftReg(n, shift_type, UInt(operand2) mod datasize);
  wX(d) := result;
}

(* CRC32B/CRC32H/CRC32W/CRC32X C=0 *)
(* CRC32CB/CRC32CH/CRC32CW/CRC32CX C=1 *)
function clause decodeData2Source ([sf]:[0]:[0]:0b11010110:Rm:0b010:[C]:sz:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  if sf == 1 & sz != 0b11 then UnallocatedEncoding();
  if sf == 0 & sz == 0b11 then UnallocatedEncoding();
  ([:'D:]) size := lsl(8, UInt(sz)); (* 2-bit size field -> 8, 16, 32, 64 *)
  (boolean) crc32c := (C == 1);

  Some(CRC(d,n,m,size,crc32c));
}

function clause execute ( CRC(d,n,m,size,crc32c) ) = {
  if ~(HaveCRCExt()) then
    UnallocatedEncoding();

  (bit[32]) acc  := rX(n); (* accumulator *)
  (bit['D]) _val := rX(m); (* input value *)
  (bit[32]) poly := if crc32c then 0x1EDC6F41 else 0x04C11DB7;

  (bit[32+'D]) tempacc := BitReverse(acc)  : (bit['D]) (Zeros());
  (bit['D+32]) tempval := BitReverse(_val) : (bit[32]) (Zeros());

  (* Poly32Mod2 on a bitstring does a polynomial Modulus over {0,1} operation *)
  wX(d) := BitReverse(Poly32Mod2(tempacc ^ tempval, poly));
}

end decodeData2Source

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        bit[32] -> option<(ast<'R,'D>)> effect pure decodeData3Source
scattered function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> decodeData3Source

(* MADD o0=0 *)
(* MSUB o0=1 *)
function clause decodeData3Source ([sf]:0b00:0b11011:0b000:Rm:[o0]:Ra:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  (reg_index) a := UInt_reg(Ra);
  ([:'R:]) destsize := if sf == 1 then 64 else 32;
  ([:'D:]) datasize := destsize;
  (boolean) sub_op := (o0 == 1);

  Some(MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op));
}

function clause execute ( MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op) ) = {
  (bit['D]) operand1 := rX(n);
  (bit['D]) operand2 := rX(m);
  (bit['R]) operand3 := rX(a);

  (integer) result := 0; (* ARM: uninitialized *)

  if sub_op then
    result := UInt(operand3) - (UInt(operand1) * UInt(operand2))
  else
    result := UInt(operand3) + (UInt(operand1) * UInt(operand2));

  wX(d) := (bit['R]) result;
}

(* SMADDL *)
(* SMSUBL *)
(* UMADDL *)
(* UMSUBL *)
function clause decodeData3Source ([1]:0b00:0b11011:[U]:0b01:Rm:[o0]:Ra:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  (reg_index) a := UInt_reg(Ra);
  ([:'R:]) destsize := 64;
  ([:'D:]) datasize := 32;
  (boolean) sub_op := (o0 == 1);
  (boolean) _unsigned := (U == 1);

  Some(MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned));
}

function clause execute ( MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned) ) = {
  (bit['D]) operand1 := rX(n);
  (bit['D]) operand2 := rX(m);
  (bit['R]) operand3 := rX(a);

  (integer) result := 0; (* ARM: uninitialized *)

  if sub_op then
    result := Int(operand3, _unsigned) - (Int(operand1, _unsigned) * Int(operand2, _unsigned))
  else
    result := Int(operand3, _unsigned) + (Int(operand1, _unsigned) * Int(operand2, _unsigned));

  wX(d) := (bit[64]) result;
}

(* SMULH *)
(* UMULH *)
function clause decodeData3Source ([1]:0b00:0b11011:[U]:0b10:Rm:[0]:Ra:Rn:Rd) = {
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  (reg_index) a := UInt_reg(Ra); (* ignored by UMULH/SMULH *)
  ([:'R:]) destsize := 64;
  ([:'D:]) datasize := destsize;
  (boolean) _unsigned := (U == 1);

  Some(MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned));
}

function clause execute ( MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned) ) = {
  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := rX(m);

  (integer) result := 0; (* ARM: uninitialized *)

  result := Int(operand1, _unsigned) * Int(operand2, _unsigned);

  wX(d) := ((bit[128]) result)[127..64];
}

end decodeData3Source

(* AND/ANDS (shifted register) *)
(* EON (shifted register) *)
(* EOR (shifted register) *)
(* ORN (shifted register) *)
(* ORR (shifted register) *)
(* BIC/BICS (shifted register) *)
function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLogicalShiftedRegister ([sf]:opc:0b01010:shift:[N]:Rm:(bit[6]) imm6:Rn:Rd) =
{
  (reg_index) d := UInt_reg(Rd);
  (reg_index) n := UInt_reg(Rn);
  (reg_index) m := UInt_reg(Rm);
  ([:'R:]) datasize := if sf == 1 then 64 else 32;
  (boolean) setflags := false; (* ARM: uninitialized *)
  (LogicalOp) op := LogicalOp_AND; (* ARM: uninitialized *)
  switch opc {
    case 0b00 -> {op := LogicalOp_AND; setflags := false}
    case 0b01 -> {op := LogicalOp_ORR; setflags := false}
    case 0b10 -> {op := LogicalOp_EOR; setflags := false}
    case 0b11 -> {op := LogicalOp_AND; setflags := true}
  };

  if sf == 0 & imm6[5] == 1 then ReservedValue();

  (ShiftType) shift_type := DecodeShift(shift);
  ([|63|]) shift_amount := UInt(imm6);
  (boolean) invert := (N == 1);

  Some(LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert))
}

function clause execute (LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert)) = {

  (bit['R]) operand1 := rX(n);
  (bit['R]) operand2 := ShiftReg(m, shift_type, shift_amount);

  if invert then operand2 := NOT(operand2);

  (bit['R]) result := 0; (* ARM: uninitialized *)
  switch op {
    case LogicalOp_AND -> result := (operand1 & operand2)
    case LogicalOp_ORR -> result := (operand1 | operand2)
    case LogicalOp_EOR -> result := (operand1 ^ operand2)
  };

  if setflags then
    wPSTATE_NZCV() := ([result[datasize - 1]]:[IsZeroBit(result)]:0b00);

  wX(d) := result;
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeDataSIMDFPoint1 ((bit[32]) machineCode) =
{
  not_implemented("decodeDataSIMDFPoint1");
  Some(Unallocated);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect {escape} decodeDataSIMDFPoint2 ((bit[32]) machineCode) =
{
  not_implemented("decodeDataSIMDFPoint2");
  Some(Unallocated);
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeDataRegister ((bit[32]) machineCode) =
{
  switch machineCode {
    case ([_]:[_]:[_]:[0]: [1]:[0]:[1]:[0]: [_]:[_]:[_]: (bit[9]) _:[_]:(bit[11]) _) -> decodeLogicalShiftedRegister(machineCode)
    case ([_]:[_]:[_]:[0]: [1]:[0]:[1]:[1]: [_]:[_]:[0]: (bit[9]) _:[_]:(bit[11]) _) -> decodeAddSubtractShiftedRegister(machineCode)
    case ([_]:[_]:[_]:[0]: [1]:[0]:[1]:[1]: [_]:[_]:[1]: (bit[9]) _:[_]:(bit[11]) _) -> decodeAddSubtractExtendedRegister(machineCode)
    case ([_]:[_]:[_]:[1]: [1]:[0]:[1]:[0]: [0]:[0]:[0]: (bit[9]) _:[_]:(bit[11]) _) -> decodeAddSubtractWithCarry(machineCode)
    case ([_]:[_]:[_]:[1]: [1]:[0]:[1]:[0]: [0]:[1]:[0]: (bit[9]) _:[0]:(bit[11]) _) -> decodeConditionalCompareRegister(machineCode)
    case ([_]:[_]:[_]:[1]: [1]:[0]:[1]:[0]: [0]:[1]:[0]: (bit[9]) _:[1]:(bit[11]) _) -> decodeConditionalCompareImmediate(machineCode)
    case ([_]:[_]:[_]:[1]: [1]:[0]:[1]:[0]: [1]:[0]:[0]: (bit[9]) _:[_]:(bit[11]) _) -> decodeConditionalSelect(machineCode)
    case ([_]:[_]:[_]:[1]: [1]:[0]:[1]:[1]: [_]:[_]:[_]: (bit[9]) _:[_]:(bit[11]) _) -> decodeData3Source(machineCode)
    case ([_]:[0]:[_]:[1]: [1]:[0]:[1]:[0]: [1]:[1]:[0]: (bit[9]) _:[_]:(bit[11]) _) -> decodeData2Source(machineCode)
    case ([_]:[1]:[_]:[1]: [1]:[0]:[1]:[0]: [1]:[1]:[0]: (bit[9]) _:[_]:(bit[11]) _) -> decodeData1Source(machineCode)
  }
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeDataImmediate ((bit[32]) machineCode) =
{
  switch machineCode {
    case ((bit[3]) _:[1]:[0]:[0]:[0]:[0]:[_]:(bit[23]) _) -> decodePCRelAddressing(machineCode)
    case ((bit[3]) _:[1]:[0]:[0]:[0]:[1]:[_]:(bit[23]) _) -> decodeAddSubtractImmediate(machineCode)
    case ((bit[3]) _:[1]:[0]:[0]:[1]:[0]:[0]:(bit[23]) _) -> decodeLogicalImmediate(machineCode)
    case ((bit[3]) _:[1]:[0]:[0]:[1]:[0]:[1]:(bit[23]) _) -> decodeMoveWideImmediate(machineCode)
    case ((bit[3]) _:[1]:[0]:[0]:[1]:[1]:[0]:(bit[23]) _) -> decodeBitfield(machineCode)
    case ((bit[3]) _:[1]:[0]:[0]:[1]:[1]:[1]:(bit[23]) _) -> decodeExtract(machineCode)
  }
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeLoadsStores ((bit[32]) machineCode) =
{
  switch machineCode {
    case ([_]:[_]:[0]:[0]: [1]:[0]:[0]:[0]: [_]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreExclusive(machineCode)
    case ([_]:[_]:[0]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadRegisterLiteral(machineCode)
    case ([_]:[_]:[1]:[0]: [1]:[_]:[0]:[0]: [0]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreNoAllocatePairOffset(machineCode)
    case ([_]:[_]:[1]:[0]: [1]:[_]:[0]:[0]: [1]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreRegisterPairPostIndexed(machineCode)
    case ([_]:[_]:[1]:[0]: [1]:[_]:[0]:[1]: [0]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreRegisterPairOffset(machineCode)
    case ([_]:[_]:[1]:[0]: [1]:[_]:[0]:[1]: [1]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreRegisterPairPreIndexed(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[0]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[0]:[0]: (bit[10]) _) -> decodeLoadStoreRegisterUnscaledImmediate(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[0]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[0]:[1]: (bit[10]) _) -> decodeLoadStoreRegisterImmediatePostIndexed(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[0]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[1]:[0]: (bit[10]) _) -> decodeLoadStoreRegisterUnprivileged(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[0]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[1]:[1]: (bit[10]) _) -> decodeLoadStoreRegisterImmediatePreIndexed(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[0]: [_]:[_]:[1]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[1]:[0]: (bit[10]) _) -> decodeLoadStoreRegisterRegisterOffset(machineCode)
    case ([_]:[_]:[1]:[1]: [1]:[_]:[0]:[1]: [_]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeLoadStoreRegisterUnsignedImmediate(machineCode)
    case ([0]:[_]:[0]:[0]: [1]:[1]:[0]:[0]: [0]:[_]:[0]:[0]: [0]:[0]:[0]:[0]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeAdvSIMDLoadStoreMultiStruct(machineCode)
    case ([0]:[_]:[0]:[0]: [1]:[1]:[0]:[0]: [1]:[_]:[0]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeAdvSIMDLoadStoreMultiStructPostIndexed(machineCode)
    case ([0]:[_]:[0]:[0]: [1]:[1]:[0]:[1]: [0]:[_]:[_]:[0]: [0]:[0]:[0]:[0]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeAdvSIMDLoadStoreSingleStruct(machineCode)
    case ([0]:[_]:[0]:[0]: [1]:[1]:[0]:[1]: [1]:[_]:[_]:[_]: [_]:[_]:[_]:[_]: (bit[4]) _:[_]:[_]: (bit[10]) _) -> decodeAdvSIMDLoadStoreSingleStructPostIndexed(machineCode)
  }
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeSystemImplementationDefined ((bit[32]) machineCode) =
{
  switch machineCode {
    case ((bit[11]) _:[0]:[1]:[_]:[_]:[_]:[1]:[_]:[1]:[1]:(bit[12]) _) -> decodeImplementationDefined(machineCode)
    case ((bit[11]) _:[1]:[1]:[_]:[_]:[_]:[1]:[_]:[1]:[1]:(bit[12]) _) -> decodeImplementationDefined(machineCode)
    case ((bit[11]) _:[_]:[_]:[_]:[_]:[_]:[_]:[_]:[_]:[_]:(bit[12]) _) -> decodeSystem(machineCode)
  }
}


function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect pure decodeBranchesExceptionSystem ((bit[32]) machineCode) =
{
  switch machineCode {
    case ([_]:[0]:[0]:[1]:[0]:[1]:[_]:[_]:[_]:[_]:(bit[22]) _) -> decodeUnconditionalBranchImmediate(machineCode)
    case ([_]:[0]:[1]:[1]:[0]:[1]:[0]:[_]:[_]:[_]:(bit[22]) _) -> decodeCompareBranchImmediate(machineCode)
    case ([_]:[0]:[1]:[1]:[0]:[1]:[1]:[_]:[_]:[_]:(bit[22]) _) -> decodeTestBranchImmediate(machineCode)
    case ([0]:[1]:[0]:[1]:[0]:[1]:[0]:[_]:[_]:[_]:(bit[22]) _) -> decodeConditionalBranchImmediate(machineCode)
    case ([1]:[1]:[0]:[1]:[0]:[1]:[0]:[0]:[_]:[_]:(bit[22]) _) -> decodeExceptionGeneration(machineCode)
    case ([1]:[1]:[0]:[1]:[0]:[1]:[0]:[1]:[0]:[0]:(bit[22]) _) -> decodeSystemImplementationDefined(machineCode)
    case ([1]:[1]:[0]:[1]:[0]:[1]:[1]:[_]:[_]:[_]:(bit[22]) _) -> decodeUnconditionalBranchRegister(machineCode)
  }
}

function forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}.
        option<(ast<'R,'D>)> effect { escape } decode ((bit[32]) machineCode) =
{
  switch machineCode {
    case ((bit[3]) _:[0]:[0]:[_]:[_]:(bit[25]) _) -> Some(Unallocated)
    case ((bit[3]) _:[1]:[0]:[0]:[_]:(bit[25]) _) -> decodeDataImmediate(machineCode)
    case ((bit[3]) _:[1]:[0]:[1]:[_]:(bit[25]) _) -> decodeBranchesExceptionSystem(machineCode)
    case ((bit[3]) _:[_]:[1]:[_]:[0]:(bit[25]) _) -> decodeLoadsStores(machineCode)
    case ((bit[3]) _:[_]:[1]:[0]:[1]:(bit[25]) _) -> decodeDataRegister(machineCode)
    case ((bit[3]) _:[0]:[1]:[1]:[1]:(bit[25]) _) -> decodeDataSIMDFPoint1(machineCode)
    case ((bit[3]) _:[1]:[1]:[1]:[1]:(bit[25]) _) -> decodeDataSIMDFPoint2(machineCode)
    case _                                        -> None
  }
}
    
end execute

val forall Nat 'R, 'R IN {32,64}, Nat 'D, 'D IN {8,16,32,64}. ast<'R,'D> -> option<(ast<'R,'D>)> effect pure supported_instructions
function option<(ast<'R,'D>)> supported_instructions ((ast<'R,'D>) instr) = {
  switch instr {
    case _ -> Some(instr)
   }
}
