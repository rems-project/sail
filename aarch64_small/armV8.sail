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



union ast ('R : Int,  /* register size */
           'D : Int),  /* data size */ 
           'R in {32, 64} & 'D in {8,16,32,64}
           =  
{
  Unallocated : unit,
  ImplementationDefinedTestBeginEnd : boolean,
  ImplementationDefinedStopFetching : unit,
  ImplementationDefinedThreadStart : unit,

  /* transactional memory, not part of the official spec */
  TMStart : reg_index,
  TMCommit : unit,
  TMAbort : (boolean,bits(5)),
  TMTest : unit,

  CompareAndBranch : (reg_index, atom('R), boolean, bits(64)),
  BranchConditional : (bits(64), bits(4)),
  GenerateExceptionEL1 : (bits(16)), /* TODO: add to .hgen */
  GenerateExceptionEL2 : (bits(16)), /* TODO: add to .hgen */
  GenerateExceptionEL3 : (bits(16)), /* TODO: add to .hgen */
  DebugBreakpoint : (bits(16)), /* TODO: add to .hgen */
  ExternalDebugBreakpoint : unit, /* TODO: add to .hgen */
  DebugSwitchToExceptionLevel : (bits(2)), /* TODO: add to .hgen */
  MoveSystemImmediate : (bits(4),PSTATEField),
  Hint : (SystemHintOp),
  ClearExclusiveMonitor : (uinteger),
  Barrier : (MemBarrierOp,MBReqDomain,MBReqTypes),
  System : (reg_index,uinteger,uinteger,uinteger,uinteger,uinteger,boolean),
  MoveSystemRegister : (reg_index,uinteger,uinteger,uinteger,uinteger,uinteger,boolean),
  TestBitAndBranch : (reg_index,atom('R),uinteger,bit,bits(64)),
  BranchImmediate : (BranchType,bits(64)),
  BranchRegister : (reg_index,BranchType),
  ExceptionReturn : unit, /* TODO: add to .hgen */
  DebugRestorePState : unit, /* TODO: add to .hgen */
  LoadLiteral : (reg_index,MemOp,boolean,uinteger,bits(64),atom('D)),
  LoadStoreAcqExc : (reg_index,reg_index,reg_index,reg_index,AccType,boolean,boolean,MemOp,uinteger,atom('R),atom('D)),
  LoadStorePairNonTemp : (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,uinteger,atom('D),bits(64)),
  LoadImmediate : (reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,bits(64),atom('R),atom('D)),
  LoadRegister : (reg_index,reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,ExtendType,uinteger,atom('R),atom('D)),
  LoadStorePair : (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,boolean,atom('D),bits(64)),
  AddSubImmediate : (reg_index,reg_index,atom('R),boolean,boolean,bits('R)),
  BitfieldMove : (reg_index,reg_index,atom('R),boolean,boolean,uinteger,uinteger,bits('R),bits('R)),
  ExtractRegister : (reg_index,reg_index,reg_index,('R),uinteger),
  LogicalImmediate : (reg_index,reg_index,('R),boolean,LogicalOp,bits('R)),
  MoveWide : (reg_index,('R),bits(16),uinteger,MoveWideOp),
  Address : (reg_index,boolean,bits(64)),
  AddSubExtendRegister : (reg_index,reg_index,reg_index,atom('R),boolean,boolean,ExtendType,range(0,7)),
  AddSubShiftedRegister : (reg_index,reg_index,reg_index,atom('R),boolean,boolean,ShiftType,range(0,63)),
  AddSubCarry : (reg_index,reg_index,reg_index,atom('R),boolean,boolean),
  ConditionalCompareImmediate : (reg_index,atom('R),boolean,bits(4),bits(4),bits('R)),
  ConditionalCompareRegister : (reg_index,reg_index,atom('R),boolean,bits(4),bits(4)),
  ConditionalSelect : (reg_index,reg_index,reg_index,atom('R),bits(4),boolean,boolean),
  Reverse : (reg_index,reg_index,atom('R),RevOp),
  CountLeading : (reg_index,reg_index,atom('R),CountOp),
  Division : (reg_index,reg_index,reg_index,atom('R),boolean),
  Shift : (reg_index,reg_index,reg_index,atom('R),ShiftType),
  CRC : (reg_index,reg_index,reg_index,atom('D),boolean),
  MultiplyAddSub : (reg_index,reg_index,reg_index,reg_index,atom('R),atom('D),boolean),
  MultiplyAddSubLong : (reg_index,reg_index,reg_index,reg_index,atom('R),atom('D),boolean,boolean),
  MultiplyHigh : (reg_index,reg_index,reg_index,reg_index,atom('R),atom('D),boolean),
  LogicalShiftedRegister : (reg_index,reg_index,reg_index,atom('R),boolean,LogicalOp,ShiftType,range(0,63),boolean),
}

val execute : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}. ast('R,'D) -> unit effect {rreg,wreg,rmem,barr,eamem,wmv,exmem,escape}
scattered function execute

/* TSTART - dummy decoding */
val decodeTMStart : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}. bits(5) -> option (ast('R,'D))
function decodeTMStart (Rt) = {
  t : reg_index = UInt_reg(Rt);
  Some(TMStart(t));
}

/* transactional memory, not part of the official spec */
function clause execute (TMStart(t)) = {
  nesting : bits(8) = TxNestingLevel;

  if nesting <_u TXIDR_EL0.DEPTH then {
    TxNestingLevel = nesting + 1;
    status : bits(64) = 0;
    if nesting == 0 then
      status = TMStartEffect; /* fake effect */
    wX(t) = status;
  } else {
    status : bits(64) = 0;
    status[10] = 1; /* set the NEST bit */
    TMAbortEffect = status; /* fake effect */
  }
}

/* external */ val TMCommitEffect : unit -> unit effect {barr}

/* TCOMMIT - dummy decoding */
val decodeTMCommit : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        unit -> option(ast('R,'D)) effect pure
function decodeTMCommit () = {
  Some(TMCommit);
}

/* transactional memory, not part of the official spec */
function clause execute (TMCommit) = {
  nesting : bits(8) = TxNestingLevel;

  if nesting == 1 then
    TMCommitEffect() /* fake effect */
  else if nesting == 0 then
    AArch64_UndefinedFault();

  TxNestingLevel = nesting - 1;
}

/* TTEST - dummy decoding */
val decodeTMTest : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        unit -> option(ast('R,'D)) effect pure 
function decodeTMTest () = {
  Some(TMTest);
}

/* transactional memory, not part of the official spec */
function clause execute (TMTest) = {
  if TxNestingLevel > 0 then
    wPSTATE_NZCV() = 0b0000
  else
    wPSTATE_NZCV() = 0b0100
}

/* TABORT - dummy decoding */
val decodeTMAbort : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(6) -> option(ast('R,'D)) effect pure 
function decodeTMAbort ([R] @ (imm5 : bits(5))) = {
  Some(TMAbort(R,imm5));
}

/* transactional memory, not part of the official spec */
function clause execute (TMAbort(retry,reason)) = {
  if TxNestingLevel > 0 then {
    status : bits(64) = 0;
    status[4..0] = reason; /* REASON */
    status[8] = retry; /* RTRY */
    status[9] = 1; /* ABRT */
    TMAbortEffect = status; /* fake effect */
  };
}

/* CBNZ */
/* CBZ */
val decodeCompareBranchImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeCompareBranchImmediate ([sf]@0b011010@[op]@(imm19:bits(19))@Rt) = {
  t : reg_index = UInt_reg(Rt);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  iszero : boolean = (op == 0);
  offset : bits(64) = SignExtend(imm19@0b00);

  Some(CompareAndBranch(t,datasize,iszero,offset));
}

function clause execute (CompareAndBranch(t,datasize,iszero,offset)) = {
  operand1 : bits('R) = rX(t);
  if IsZero(operand1) == iszero then
    BranchTo(rPC() + offset, BranchType_JMP);
}

/* B.cond */
val decodeConditionalBranchImmediate: forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
      bits(32) -> option(ast('R,'D)) effect pure
function decodeConditionalBranchImmediate (0b0101010@0b0@(imm19 : bits(19))@0b0@ _cond) =
{
  offset : bits(64) = SignExtend(imm19@0b00);
  condition : bits(4) = _cond;

  Some(BranchConditional(offset,condition));
}

function clause execute (BranchConditional(offset,condition)) = {
  if ConditionHolds(condition) then
    BranchTo(rPC() + offset, BranchType_JMP);
}


val decodeExceptionGeneration : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
scattered function decodeExceptionGeneration

/* SVC */
function clause decodeExceptionGeneration (0b11010100@0b000@(imm16 : bits(16))@0b000@0b01) = {
  imm : bits(16) = imm16;
  Some(GenerateExceptionEL1(imm))
}

function clause execute (GenerateExceptionEL1(imm)) = {
  AArch64_CallSupervisor(imm);
}

/* HVC */
function clause decodeExceptionGeneration (0b11010100@0b000@(imm16 : bits(16))@0b000@0b10) = {
  imm : bits(16) = imm16;
  Some(GenerateExceptionEL2(imm))
}

function clause execute (GenerateExceptionEL2(imm)) =
{
  if ~(HaveEL(EL2)) | PSTATE_EL == EL0 | (PSTATE_EL == EL1 & IsSecure()) then
    UnallocatedEncoding();

  hvc_enable : bit = if HaveEL(EL3) then SCR_EL3.HCE else NOT'(HCR_EL2.HCD);
  if hvc_enable == 0 then
    AArch64_UndefinedFault()
  else
    AArch64_CallHypervisor(imm);
}

/* SMC */
function clause decodeExceptionGeneration (0b11010100@0b000@(imm16 : bits(16))@0b000@0b11) = {
  imm : bits(16) = imm16;
  Some(GenerateExceptionEL3(imm))
}

function clause execute (GenerateExceptionEL3(imm)) = {
  if ~(HaveEL(EL3)) | PSTATE_EL == EL0 then
    UnallocatedEncoding();

  AArch64_CheckForSMCTrap(imm);

  if SCR_EL3.SMD == 1 then
    /* SMC disabled */
    AArch64_UndefinedFault()
  else
    AArch64_CallSecureMonitor(imm);
}

/* BRK */
function clause decodeExceptionGeneration (0b11010100@0b001@(imm16 : bits(16))@0b000@0b00) = {
  comment : bits(16) = imm16;
  Some(DebugBreakpoint(comment))
}

function clause execute (DebugBreakpoint(comment)) = {
  AArch64_SoftwareBreakpoint(comment);
}

/* HLT */
function clause decodeExceptionGeneration (0b11010100@0b010@(imm16 : bits(16))@0b000@0b00) = {
  /* FIXME: we don't allow register reads in the decoding, but we probably should */
  /* ARM: if EDSCR.HDE == 0 | ~(HaltingAllowed()) then AArch64_UndefinedFault(); /* ARM: UndefinedFault() */ */

  Some(ExternalDebugBreakpoint);
}


function clause execute (ExternalDebugBreakpoint) = {
  Halt(DebugHalt_HaltInstruction);
}

/* DCPS1 LL=0b01*/
/* DCPS2 LL=0b10*/
/* DCPS3 LL=0b11*/
function clause decodeExceptionGeneration (0b11010100@0b101@(imm16 : bits(16))@0b000@(LL : bits(2))) = {
  target_level : bits(2) = LL;
  if LL == 0b00 then UnallocatedEncoding();
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: if ~(Halted()) then AArch64_UndefinedFault(); */

  Some(DebugSwitchToExceptionLevel(target_level));
}

function clause execute (DebugSwitchToExceptionLevel(target_level)) = {
  DCPSInstruction(target_level);
}

end decodeExceptionGeneration

val decodeSystem : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
scattered function decodeSystem

/* MSR (immediate) */
function clause decodeSystem (0b1101010100@[0]@0b00@(op1 : bits(3))@0b0100@CRm@(op2 : bits(3))@0b11111) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess(0b00, op1, 0b0100, CRm, op2, 0b11111, 0); */

  operand : bits(4) = CRm;
  field : PSTATEField = 0; /* ARM: uninitialized */
  match op1@op2 {
    (0b000@0b101)  => field = PSTATEField_SP,
    (0b011@0b110)  => field = PSTATEField_DAIFSet,
    (0b011@0b111)  => field = PSTATEField_DAIFClr,
    _  => UnallocatedEncoding()
  };

  /* FIXME: we don't allow register reads in the decoding */
  /* FIXME: it is not clear why this check is here. How is it different
            than the CheckSystemAccess above? */
  /*Check that an AArch64 MSR/MRS access to the DAIF flags is permitted*/
  /* ARM: if op1 == 0b011 & PSTATE_EL == EL0 & SCTLR_EL1.UMA == 0 then
    AArch64_SystemRegisterTrap(EL1, 0b00, op2, op1, 0b0100, 0b11111, CRm, 0);*/

  Some(MoveSystemImmediate(operand,field));
}

function clause execute ( MoveSystemImmediate(operand,field) ) = {
  match field {
    PSTATEField_SP  => PSTATE_SP = operand[0],
    PSTATEField_DAIFSet  => {
      PSTATE_D = (PSTATE_D | operand[3]);
      PSTATE_A = (PSTATE_A | operand[2]);
      PSTATE_I = (PSTATE_I | operand[1]);
      PSTATE_F = (PSTATE_F | operand[0]);
    },
    PSTATEField_DAIFClr  => {
      PSTATE_D = (PSTATE_D & NOT'(operand[3]));
      PSTATE_A = (PSTATE_A & NOT'(operand[2]));
      PSTATE_I = (PSTATE_I & NOT'(operand[1]));
      PSTATE_F = (PSTATE_F & NOT'(operand[0]));
    }
  }
}

/* HINT */
function clause decodeSystem (0b1101010100@[0]@0b00@0b011@0b0010@(CRm : bits(4))@(op2 : bits(3))@0b11111) = {
  op : SystemHintOp = 0; /* ARM: uninitialized */

  match CRm@op2 {
    (0b0000@0b000)  => op = SystemHintOp_NOP,
    (0b0000@0b001)  => op = SystemHintOp_YIELD,
    (0b0000@0b010)  => op = SystemHintOp_WFE,
    (0b0000@0b011)  => op = SystemHintOp_WFI,
    (0b0000@0b100)  => op = SystemHintOp_SEV,
    (0b0000@0b101)  => op = SystemHintOp_SEVL,
    _  => op = SystemHintOp_NOP
  };

  Some(Hint(op));
}

function clause execute ( Hint(op) ) = {
  match op {
    SystemHintOp_YIELD  =>
      Hint_Yield(),

    SystemHintOp_WFE  => {
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
    },

    SystemHintOp_WFI  => {
      if ~(InterruptPending()) then {
        if PSTATE_EL == EL0 then
          AArch64_CheckForWFxTrap(EL1, false);
        if HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL == EL0 | PSTATE_EL == EL1) then
          AArch64_CheckForWFxTrap(EL2, false);
        if HaveEL(EL3) & PSTATE_EL != EL3 then
          AArch64_CheckForWFxTrap(EL3, false);
        WaitForInterrupt();
      };
    },

    SystemHintOp_SEV  =>
      SendEvent(),

    SystemHintOp_SEVL  =>
      EventRegisterSet(),

    _  => () /* do nothing */
  }
}

/* CLREX */
function clause decodeSystem (0b1101010100@[0]@0b00@0b011@0b0011@(CRm : bits(4))@0b010@0b11111) = {
  /* ARM: // CRm field is ignored */
  imm : uinteger = CRm; /* we need CRm for pretty printing */
  Some(ClearExclusiveMonitor(imm));
}

function clause execute (ClearExclusiveMonitor(imm)) = {
  ClearExclusiveLocal(ProcessorID());
}

/* DMB opc=0b01*/
/* DSB opc=0b00*/
/* ISB opc=0b10*/
function clause decodeSystem (0b1101010100@[0]@0b00@0b011@0b0011@(CRm : bits(4))@[1]@opc@0b11111) = {
  /* TODO: according to ARM, HCR_EL2.BSU affect the domain, but the pseudo
           code doesn't show any signs of that */
  op : MemBarrierOp = 0; /* ARM: uninitialized */
  domain : MBReqDomain = 0; /* ARM: uninitialized */
  types : MBReqTypes = 0; /* ARM: uninitialized */

  match opc {
    0b00  => op = MemBarrierOp_DSB,
    0b01  => op = MemBarrierOp_DMB,
    0b10  => op = MemBarrierOp_ISB,
    _  => UnallocatedEncoding()
  };

  match CRm[3..2] {
    0b00  => domain = MBReqDomain_OuterShareable,
    0b01  => domain = MBReqDomain_Nonshareable,
    0b10  => domain = MBReqDomain_InnerShareable,
    0b11  => domain = MBReqDomain_FullSystem
  };

  match CRm[1..0] {
    0b01  => types = MBReqTypes_Reads,
    0b10  => types = MBReqTypes_Writes,
    0b11  => types = MBReqTypes_All,
    _  => {
      types = MBReqTypes_All;
      domain = MBReqDomain_FullSystem;
    }
  };

  Some(Barrier(op,domain,types));
}

function clause execute ( Barrier(op,domain,types) ) = {
  match op {
    MemBarrierOp_DSB  =>
      DataSynchronizationBarrier(domain, types),
    MemBarrierOp_DMB  =>
      DataMemoryBarrier(domain, types),
    MemBarrierOp_ISB  =>
      InstructionSynchronizationBarrier()
  };
}

/* SYS L=0b0 */
/* SYSL L=0b1 */
function clause decodeSystem (0b1101010100@[L]@0b01@(op1 : bits(3))@(CRn : bits(4))@(CRm : bits(4))@(op2 : bits(3))@Rt) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess(0b01, op1, CRn, CRm, op2, Rt, L);*/

  t : reg_index = UInt_reg(Rt);

  sys_op0 : uinteger = 1;
  sys_op1 : uinteger = UInt(op1);
  sys_op2 : uinteger = UInt(op2);
  sys_crn : uinteger = UInt(CRn);
  sys_crm : uinteger = UInt(CRm);
  has_result : boolean = (L == 1);

  Some(System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result));
}

function clause execute ( System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result) ) =
{
  if has_result then
    wX(t) = SysOp_R(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    SysOp_W(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

/* MRS L=1 */
/* MSR (register) L=0 */
function clause decodeSystem (0b1101010100@[L]@[1]@[o0]@(op1 : bits(3))@(CRn : bits(4))@(CRm : bits(4))@(op2 : bits(3))@Rt) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess([0b1]:[o0], op1, CRn, CRm, op2, Rt, L); */

  t : reg_index = UInt_reg(Rt);

  sys_op0 : uinteger = 2 + UInt([o0]);
  sys_op1 : uinteger = UInt(op1);
  sys_op2 : uinteger = UInt(op2);
  sys_crn : uinteger = UInt(CRn);
  sys_crm : uinteger = UInt(CRm);
  read : boolean = (L == 1);

  Some(MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read));
}

function clause execute ( MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read) ) = {
  if read then
    wX(t) = System_Get(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    System_Put(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

end decodeSystem

val decodeImplementationDefined : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
scattered function decodeImplementationDefined

/* instructions to signal to Sail that test begins/ends */
function clause decodeImplementationDefined (0b1101010100@[0]@0b01@0b011@[1]@[_]@0b11@0b0000@0b000@0b0000@[isEnd]) = {
  Some(ImplementationDefinedTestBeginEnd(isEnd));
}

function clause execute ( ImplementationDefinedTestBeginEnd(isEnd) ) = {
  if isEnd then
    info("test ends")
  else
    info("test begins");
}

/* instructions to signal ppcmem to stop fetching */
function clause decodeImplementationDefined (0b1101010100@[0]@0b01@0b011@[1]@[_]@0b11@0b0000@0b000@0b00010) = {
  Some(ImplementationDefinedStopFetching)
}

function clause execute ( ImplementationDefinedStopFetching ) = {
  info("stop fetching instructions");
}

/* instructions to signal ppcmem to start a thread */
function clause decodeImplementationDefined (0b1101010100@[0]@0b01@0b011@[1]@[_]@0b11@0b0000@0b000@0b00011) = {
  Some(ImplementationDefinedThreadStart)
}

function clause execute ( ImplementationDefinedThreadStart ) = {
  info("thread start");
}

end decodeImplementationDefined

/* TBNZ */
/* TBZ */
val decodeTestBranchImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeTestBranchImmediate ([b5]@0b011011@[op]@(b40 : bits(5))@(imm14 : bits(14))@Rt) = {
  t : reg_index = UInt_reg(Rt);

  datasize : atom('R) = if b5 == 1 then 64 else 32;
  bit_pos : uinteger = UInt([b5]:b40);
  bit_val : bit = op;
  offset : bits(64) = SignExtend(imm14@0b00);

  Some(TestBitAndBranch(t,datasize,bit_pos,bit_val,offset));
}

function clause execute ( TestBitAndBranch(t,datasize,bit_pos,bit_val,offset) ) = {
  operand : bits('R) = rX(t);

  if operand[bit_pos] == bit_val then
    BranchTo(rPC() + offset, BranchType_JMP);
}

/* B */
/* BL */
val decodeUnconditionalBranchImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeUnconditionalBranchImmediate ([op]@0b00101@(imm26 : bits(26))) = {
  branch_type : BranchType = if op == 1 then BranchType_CALL else BranchType_JMP;
  offset : bits(64) = SignExtend(imm26@0b00);

  Some(BranchImmediate(branch_type,offset));
}

function clause execute (BranchImmediate(branch_type,offset)) = {
  if branch_type == BranchType_CALL then wX(30) = rPC() + 4;

  BranchTo(rPC() + offset, branch_type);
}


val decodeUnconditionalBranchRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape} 
scattered function decodeUnconditionalBranchRegister

/* BLR */
/* BR */
/* RET */
function clause decodeUnconditionalBranchRegister (0b1101011@0b00@op@0b11111@0b000000@Rn@0b00000) = {
  n : reg_index = UInt_reg(Rn);
  branch_type : BranchType = 0; /* ARM: uninitialized */

  match op {
    0b00  => branch_type = BranchType_JMP,
    0b01  => branch_type = BranchType_CALL,
    0b10  => branch_type = BranchType_RET,
    _  => UnallocatedEncoding()
  };

  Some(BranchRegister(n,branch_type));
}

function clause execute (BranchRegister(n,branch_type)) = {
  target : bits(64) = rX(n);

  if branch_type == BranchType_CALL then wX(30) = rPC() + 4;
  BranchTo(target, branch_type);
}

/* ERET */
function clause decodeUnconditionalBranchRegister (0b1101011@0b0100@0b11111@0b000000@0b11111@0b00000) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: if PSTATE_EL == EL0 then UnallocatedEncoding(); */

  Some(ExceptionReturn);
}

function clause execute (ExceptionReturn) = {
  AArch64_ExceptionReturn(rELR'(), rSPSR());
}

/* DRPS */
function clause decodeUnconditionalBranchRegister (0b1101011@0b0101@0b11111@0b000000@0b11111@0b00000) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: if ~(Halted()) | PSTATE_EL == EL0 then UnallocatedEncoding(); */

  Some(DebugRestorePState);
}

function clause execute (DebugRestorePState) = {
  DRPSInstruction();
}

end decodeUnconditionalBranchRegister

val decodeAdvSIMDLoadStoreMultiStruct : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeAdvSIMDLoadStoreMultiStruct (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreMultiStruct");
  Some(Unallocated);
}

val decodeAdvSIMDLoadStoreMultiStructPostIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeAdvSIMDLoadStoreMultiStructPostIndexed (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreMultiStructPostIndexed");
  Some(Unallocated);
}

val decodeAdvSIMDLoadStoreSingleStruct : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeAdvSIMDLoadStoreSingleStruct (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreSingleStruct");
  Some(Unallocated);
}

val decodeAdvSIMDLoadStoreSingleStructPostIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeAdvSIMDLoadStoreSingleStructPostIndexed (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreSingleStructPostIndexed");
  Some(Unallocated);
}

/* LDR (literal) opc=0b0_ */
/* LDRSW (literal) opc=0b10 */
/* PRFM (literal) opc=0b11 */
val decodeLoadRegisterLiteral : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D))
function  decodeLoadRegisterLiteral ((opc : bits(2))@0b011@[0]@0b00@(imm19 : bits(19))@Rt) = {
  t : reg_index = UInt_reg(Rt);
  memop : MemOp = MemOp_LOAD;
  _signed : boolean = false;
  size : uinteger = 0; /* ARM: uninitialized */
  offset : bits(64) = 4; /* ARM: uninitialized */

  match opc {
    0b00  =>
      size = 4, /* LDR (literal) 32 */
    0b01  =>
      size = 8, /* LDR (literal) 64 */
    0b10  => { /* LDRSW (literal) */
      size = 4;
      _signed = true;
    },
    0b11  => /* PRFM (literal) */
      memop = MemOp_PREFETCH
  };

  offset = SignExtend(imm19@0b00);

  datasize : atom('D) = size*8; /* not in ARM ARM */

  Some(LoadLiteral(t,memop,_signed,size,offset,datasize));
}

function clause execute ( LoadLiteral(t,memop,_signed,size,offset,(datasize : atom('D))) ) = {
  address : bits(64) = rPC() + offset;
  data : bits('D) = 0; /* ARM: uninitialized */

  match memop {
    MemOp_LOAD  => {
      data = flush_read_buffer(
        rMem(empty_read_buffer, address, size, AccType_NORMAL),
        size
      );
      if _signed then
        wX(t) = SignExtend(data) : bits(64)
      else
        wX(t) = data;
    },
    MemOp_PREFETCH  =>
      Prefetch(address,t : bits(5))
  };
}

/* LDAR   size=0b1_,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDARB  size=0b00,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDARH  size=0b01,o2=1,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDAXP  size=0b1_,o2=0,L=1,o1=1,o0=1,rs=(1)(1)(1)(1)(1)                     */
/* LDAXR  size=0b1_,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDAXRB size=0b00,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDAXRH size=0b01,o2=0,L=1,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDXP   size=0b1_,o2=0,L=1,o1=1,o0=0,rs=(1)(1)(1)(1)(1)                     */
/* LDXR   size=0b1_,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDXRB  size=0b00,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* LDXRH  size=0b01,o2=0,L=1,o1=0,o0=0,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* STLR   size=0b1_,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* STLRB  size=0b00,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* STLRH  size=0b01,o2=1,L=0,o1=0,o0=1,rs=(1)(1)(1)(1)(1),rt2=(1)(1)(1)(1)(1) */
/* STLXP  size=0b1_,o2=0,L=0,o1=1,o0=1                                        */
/* STLXR  size=0b1_,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) */
/* STLXRB size=0b00,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) */
/* STLXRH size=0b01,o2=0,L=0,o1=0,o0=1,                   rt2=(1)(1)(1)(1)(1) */
/* STXP   size=0b1_,o2=0,L=0,o1=1,o0=0                                        */
/* STXR   size=0b1_,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) */
/* STXRB  size=0b00,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) */
/* STXRH  size=0b01,o2=0,L=0,o1=0,o0=0,                   rt2=(1)(1)(1)(1)(1) */
val decodeLoadStoreExclusive : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreExclusive ((size : bits(2))@0b001000@[o2]@[L]@[o1]@Rs@[o0]@Rt2@Rn@Rt) = {
  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  t2 : reg_index = UInt_reg(Rt2); /* ignored by load/store single register */
  s : reg_index= UInt_reg(Rs);   /* ignored by all loads and store-release */

  if ([o2,o1,o0]) == 0b100 | ([o2,o1] == 0b11) then UnallocatedEncoding();
  if o1 == 1 & size[1] == 0 then UnallocatedEncoding();

  acctype : AccType = if o0 == 1 then AccType_ORDERED else AccType_ATOMIC;
  excl : boolean = (o2 == 0);
  pair : boolean = (o1 == 1);
  memop : MemOp = if L == 1 then MemOp_LOAD else MemOp_STORE;
  elsize = lsl(8, UInt(size));
  regsize : atom('R) = if elsize == 64 then 64 else 32;
  datasize : atom('D) = if pair then elsize * 2 else elsize;

  /* lemma: pair --> datasize = 2*regsize */
  /* follows from "if o1 == 1 & size[1] == 0 then UnallocatedEncoding();" */

  Some(LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,datasize));
}

function clause execute ( LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,(datasize :atom('D)) )) = {
  address : bits(64) = 0; /* ARM: uninitialized */
  data : bits('D) = 0; /* ARM: uninitialized */
  /*constant*/ dbytes : uinteger = quot (datasize,8);
  rt_unknown : boolean = false;
  rn_unknown : boolean = false;

  if memop == MemOp_LOAD & pair & t == t2 then {
    UnallocatedEncoding(); /* ARM:
    (Constraint) c = ConstrainUnpredictable();
    assert( vIN(c, [Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP]) );
    switch c {
      Constraint_UNKNOWN  => rt_unknown =: true /* result is UNKNOWN */
      Constraint_UNDEF  =>   UnallocatedEncoding()
      Constraint_NOP  =>     EndOfInstruction()
    };*/
  };

  if memop == MemOp_STORE & excl then {
    if s == t | (pair & s == t2) then {
      UnallocatedEncoding(); /* ARM:
      (Constraint) c = ConstrainUnpredictable();
      assert( vIN(c, [Constraint_UNKNOWN, Constraint_NONE, Constraint_UNDEF, Constraint_NOP]) );
      switch c {
        Constraint_UNKNOWN  => rt_unknown = true  /* store UNKNOWN value */
        Constraint_NONE  =>    rt_unknown = false /* store original value */
        Constraint_UNDEF  =>   UnallocatedEncoding()
        Constraint_NOP  =>     EndOfInstruction()
      };*/
    };
    if s == n & n != 31 then {
      UnallocatedEncoding(); /* ARM:
      (Constraint) c = ConstrainUnpredictable();
      assert( vIN(c, [Constraint_UNKNOWN, Constraint_NONE, Constraint_UNDEF, Constraint_NOP]) );
      switch c {
        Constraint_UNKNOWN  => rn_unknown = true  /* address is UNKNOWN */
        Constraint_NONE  =>    rn_unknown = false /* address is original base */
        Constraint_UNDEF  =>   UnallocatedEncoding()
        Constraint_NOP  =>     EndOfInstruction()
      };*/
    };
  };

  /* this is a hack to allow the result of store-exclusive to be observed
  before anything else */
  status : bit = 0;
  if memop == MemOp_STORE & excl then {
    /*(bit)*/ status = if speculate_exclusive_success() then 0 else 1;
    wX(s) = ZeroExtend([status]) : bits(32);

    /* should be:
    if status == 1 then return ();
    */
  };
  if status == 1 then () else {

  if n == 31 then {
    CheckSPAlignment();
    address = rSP();
  } else if rn_unknown then
    address = UNKNOWN : bits(64)
  else
    address = rX(n);

  match memop {
    MemOp_STORE  => {
      /* anounce the address */
      wMem_Addr(address, dbytes, acctype, excl);

      if rt_unknown then
        data = UNKNOWN : bits('D)
      else if pair then {
        assert( excl, None );
        el1 : bits('R) = rX(t); /* ARM: bits(datasize / 2) see lemma in the decoding */
        el2 : bits('R) = rX(t2); /* ARM: bits(datasize / 2) see lemma in the decoding */
        data = if BigEndian() then el1:el2 else el2:el1;
      } else
        data : bits('D) = rX(t);

      if excl then {
        /* store {release} exclusive register|pair (atomic) */
        status : bit = 1;
        /* Check whether the Exclusive Monitors are set to include the */
        /* physical memory locations corresponding to virtual address */
        /* range [address, address+dbytes-1]. */
        if AArch64_ExclusiveMonitorsPass(address, dbytes) then {
          /* This atomic write will be rejected if it does not refer */
          /* to the same physical locations after address translation. */
          /* ARM: wMem(address, dbytes, acctype) = data;
          status = ExclusiveMonitorsStatus(); */
          status = flush_write_buffer_exclusive(
            wMem_exclusive(empty_write_buffer, address, dbytes, acctype, data)
          );
        };
        /* ARM: the following code was moved up, see note there
        wX(s) = (bits(32)) (ZeroExtend([status]));
        */
      } else {
        /* store release register (atomic) */
        flush_write_buffer(
          wMem(empty_write_buffer, address, dbytes, acctype, data)
        );
      };
    },

    MemOp_LOAD  => {
      if excl then {
        /* Tell the Exclusive Monitors to record a sequence of one or more atomic */
        /* memory reads from virtual address range [address, address+dbytes-1]. */
        /* The Exclusive Monitor will only be set if all the reads are from the */
        /* same dbytes-aligned physical address, to allow for the possibility of */
        /* an atomicity break if the translation is changed between reads. */
        AArch64_SetExclusiveMonitors(address, dbytes);
      };

      if pair then {
        /* load exclusive pair */
        assert( excl, None );
        if rt_unknown then
          /* ConstrainedUNPREDICTABLE case */
          wX(t) = UNKNOWN : bits('D)
        else if elsize == 32 then {
          /* 32-bit load exclusive pair (atomic) */
          data = flush_read_buffer(
            rMem_exclusive(empty_read_buffer, address, dbytes, acctype),
            dbytes
          );
          if BigEndian() then {
            wX(t) = data[(datasize - 1)..elsize];
            wX(t2) = data[(elsize - 1)..0];
          } else {
            wX(t) = data[(elsize - 1)..0];
            wX(t2) = data[(datasize - 1)..elsize];
          };
        } else { /* elsize == 64 */
          /* 64-bit load exclusive pair (not atomic), */
          /* but must be 128-bit aligned */
          if address != Align(address, dbytes) then {
            iswrite : boolean = false;
            secondstage : boolean = false;
            AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
          };
          read_buffer : read_buffer_type = rMem_exclusive(empty_read_buffer, address + 0, 8, acctype);
                             read_buffer = rMem_exclusive(read_buffer,       address + 8, 8, acctype);
          value : bits(128) = flush_read_buffer(read_buffer, 8*2);
          wX(t) = value[63..0];
          wX(t2) = value[127..64];
        };
      } else {
        /* load {acquire} {exclusive} single register */
        data = flush_read_buffer(
          rMem'(empty_read_buffer, address, dbytes, acctype, excl),
          dbytes
        );
        wX(t) = ZeroExtend(data) : bits('R);
      };
    }
  };
  };
}

/* LDNP */
/* STNP */
val decodeLoadStoreNoAllocatePairOffset : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreNoAllocatePairOffset ((opc : bits(2))@0b101@[0]@0b000@[L]@(imm7 : bits(7))@Rt2@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;

  /* Shared decode */

  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  t2 : reg_index = UInt_reg(Rt2);
  acctype : AccType = AccType_STREAM;
  memop : MemOp = if L == 1 then MemOp_LOAD else MemOp_STORE;
  if opc[0] == 1 then UnallocatedEncoding();
  scale : uinteger = 2 + UInt([opc[1]]);
  datasize : atom('D) = lsl(8, scale);
  offset : bits(64) = LSL(SignExtend(imm7), scale);

  Some(LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,datasize,offset));
}

function clause execute ( LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,(datasize : atom('D)),offset) ) = {
  address : bits(64) = 0; /* ARM: uninitialized */
  data1 : bits('D) = 0; /* ARM: uninitialized */
  data2 : bits('D) = 0; /* ARM: uninitialized */
  /*constant*/ dbytes : uinteger = quot(datasize,8);
  rt_unknown : boolean = false;

  if memop == MemOp_LOAD & t == t2 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert c IN {Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP};

    case c of
      when Constraint_UNKNOWN rt_unknown = TRUE; // result is UNKNOWN
      when Constraint_UNDEF   UnallocatedEncoding();
      when Constraint_NOP     EndOfInstruction();
    };*/
  };

  if n == 31 then {
    CheckSPAlignment();
    address = rSP();
  } else
    address = rX(n);

  if ~(postindex) then
    address = address + offset;

  if memop == MemOp_STORE then
    /* anounce the address */
    wMem_Addr(address, dbytes * 2, acctype, false);

  /* this is a hack to allow the address write back to be observed
     before the memory access */
  if wback then {
    let address' = (if ~(postindex) then address else (address + offset)) : bits(64) in
    if n == 31 then
      wSP() = address'
    else
      wX(n) = address'
  };

  match memop {
    MemOp_STORE  => {
      if rt_unknown & t == n then
        data1 = UNKNOWN : bits('D)
      else
        data1 = rX(t);
      if rt_unknown & t2 == n then
        data2 = UNKNOWN : bits('D)
      else
        data2 = rX(t2);

      write_buffer : write_buffer_type = wMem(empty_write_buffer, address + 0,      dbytes, acctype, data1);
                          write_buffer = wMem(write_buffer,       address + dbytes, dbytes, acctype, data2);
      flush_write_buffer(write_buffer);
    },

    MemOp_LOAD  => {
      read_buffer : read_buffer_type = rMem(empty_read_buffer, address + 0     , dbytes, acctype);
                         read_buffer = rMem(read_buffer,       address + dbytes, dbytes, acctype);
      read_data : bits('D*2) = flush_read_buffer(read_buffer, dbytes*2);
      data1 = read_data[(datasize - 1)..0];
      data2 = read_data[((datasize * 2) - 1)..datasize];

      if rt_unknown then {
        data1 = UNKNOWN : bits('D);
        data2 = UNKNOWN : bits('D);
      };
      wX(t) = data1;
      wX(t2) = data2;
    }
  };

/* ARM: the following code was moved up, see note there
  if wback then {
    if postindex then
      address = address + offset;
    if n == 31 then
      wSP() = address
    else
      wX(n) = address;
  };
*/
}

function sharedDecodeLoadImmediate forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}. 
           (opc : bits(2),size : bits(2),Rn,Rt,wback,postindex,scale : uinteger,offset,acctype,prefetchAllowed : bool) -> option(ast('R,'D))
          = {
  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  /* ARM: inorder to unify the decoding acctype was moved out.
          AccType_UNPRIV for LDT* / STT* and AccType_NORMAL for the rest.
  acctype : AccType = AccType_NORMAL/AccType_UNPRIV; */
  memop : MemOp = 0; /* ARM: uninitialized */
  _signed : boolean = false; /* ARM: uninitialized */
  regsize : atom('R) = 64; /* ARM: uninitialized */

  if opc[1] == 0 then {
    /* store or zero-extending load */
    memop = if opc[0] == 1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    _signed = false;
  } else {
    if size == 0b11 then {
      /* ARM: we use the following if/else to unify the decoding */
      if prefetchAllowed then {
        memop = MemOp_PREFETCH;
        if opc[0] == 1 then UnallocatedEncoding();
      } else {
        /* no unprivileged prefetch */
        UnallocatedEncoding();
      };
    } else {
      /* sign-extending load */
      memop = MemOp_LOAD;
      if size == 0b10 & opc[0] == 1 then UnallocatedEncoding();
      regsize = if opc[0] == 1 then 32 else 64;
      _signed = true;
    };
  };

  datasize : atom('D) = lsl(8, scale);

  Some(LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize));
}

/* LDR/STR (immediate) post-index */
/* LDRB/STRB (immediate) post-index */
/* LDRH/STRH (immediate) post-index */
/* LDRSB (immediate) post-index */
/* LDRSH (immediate) post-index */
/* LDRSW (immediate) post-index */
val decodeLoadStoreRegisterImmediatePostIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterImmediatePostIndexed (size@0b111@[0]@0b00@opc@[0]@(imm9 : bits(9))@0b01@Rn@Rt) = {
  wback : boolean = true;
  postindex : boolean = true;
  scale : uinteger = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

function clause execute ( LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize : atom('D)) ) = {
  address : bits(64) = 0; /* ARM: uninitialized */
  data : bits('D) = 0; /* ARM: uninitialized */
  wb_unknown : boolean = false;
  rt_unknown : boolean = false;

  if memop == MemOp_LOAD & wback & n == t & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_WBSUPPRESS  => wback = false     /* writeback is suppressed */
      Constraint_UNKNOWN  =>    wb_unknown = true /* writeback is UNKNOWN */
        Constraint_UNDEF  =>      UnallocatedEncoding()
        Constraint_NOP  =>        EndOfInstruction()
    };*/
  };

  if memop == MemOp_STORE & wback & n == t & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_NONE  =>    rt_unknown = false (* value stored is original value *)
      Constraint_UNKNOWN  => rt_unknown = true  (* value stored is UNKNOWN *)
        Constraint_UNDEF  =>   UnallocatedEncoding()
        Constraint_NOP  =>     EndOfInstruction()
    };*/
  };

  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment();
    address = rSP();
  } else
    address = rX(n);

  if ~(postindex) then
    address = address + offset;

  if memop == MemOp_STORE then
    /* anounce the address */
    wMem_Addr(address, quot (datasize,8), acctype, false);

  /* this is a hack to allow the address write back to be observed
     before the memory access */
  if wback then {
    let address' = (if ~(postindex) then address else (address + offset)) : bits(64) in
    if n == 31 then
      wSP() = address'
    else
      wX(n) = address'
  };

  match memop {
    MemOp_STORE  => {
      if rt_unknown then
        data = UNKNOWN : bits('D)
      else
        data = rX(t);

      flush_write_buffer(
        wMem(empty_write_buffer, address, quot(datasize,8), acctype, data)
      );
    },

    MemOp_LOAD  => {
      data = flush_read_buffer(
        rMem(empty_read_buffer, address, quot(datasize,8), acctype),
        quot(datasize, 8)
      );
      if _signed then
        wX(t) = SignExtend(data) : bits('R) /* ARM: regsize */
      else
        wX(t) = ZeroExtend(data) : bits('R); /* ARM: regsize */
    },

    MemOp_PREFETCH  =>
      Prefetch(address,t : bits(5))
  };

/* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address = (bits(64)) UNKNOWN
    else if postindex then
      address = address + offset;
    if n == 31 then
      wSP() = address
    else
      wX(n) = address;
  };
*/
}

/* LDR/STR (immediate) pre-index */
/* LDRB/STRB (immediate) pre-index */
/* LDRH/STRH (immediate) pre-index */
/* LDRSB (immediate) pre-index */
/* LDRSH (immediate) pre-index */
/* LDRSW (immediate) pre-index */
val decodeLoadStoreRegisterImmediatePraeIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterImmediatePreIndexed (size@0b111@[0]@0b00@opc@[0]@(imm9 : bits(9))@0b11@Rn@Rt) = {
  wback : boolean = true;
  postindex : boolean = false;
  scale : uinteger = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

val sharedDecodeLoadRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D))
function sharedDecodeLoadRegister(Rn,Rt,Rm,opc : bits(2),size : bits(2),wback,postindex,scale : uinteger,extend_type,shift) = {
  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  m : reg_index = UInt_reg(Rm);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = 0; /* ARM: uninitialized */
  _signed : boolean = 0; /* ARM: uninitialized */
  regsize : atom('R) = 64; /* ARM: uninitialized */

  if opc[1] == 0 then {
    /* store or zero-extending load */
    memop = if opc[0] == 1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    _signed = false;
  } else {
    if size == 0b11 then {
      memop = MemOp_PREFETCH;
      if opc[0] == 1 then UnallocatedEncoding();
    } else {
      /* sign-extending load */
      memop = MemOp_LOAD;
      if size == 0b10 & opc[0] == 1 then UnallocatedEncoding();
      regsize = if opc[0] == 1 then 32 else 64;
      _signed = true;
    };
  };

  datasize : atom('D) = lsl(8, scale);

  Some(LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize));
}

/* LDR/STR (register) */
/* LDRB/STRB (register) */
/* LDRH/STRH (register) */
/* LDRSB (register) */
/* LDRSH (register) */
/* LDRSW (register) */
/* PRFM (register) */

val decodeLoadStoreRegisterRegisterOffset : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D))
function decodeLoadStoreRegisterRegisterOffset (size@0b111@[0]@0b00@opc@[1]@Rm@option_v@[S]@0b10@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : uinteger = UInt(size);
  if option_v[1] == 0 then UnallocatedEncoding(); /* sub-word index */
  extend_type : ExtendType = DecodeRegExtend(option_v);
  shift : uinteger = if S == 1 then scale else 0;

  sharedDecodeLoadRegister(Rn,Rt,Rm,opc,size,wback,postindex,scale,extend_type,shift);
}

function clause execute ( LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize : atom('D)) ) = {
  offset : bits(64) = ExtendReg(m, extend_type, shift);
  address : bits(64) = 0; /* ARM: uninitialized */
  data : bits('D) = 0; /* ARM: uninitialized */
  wb_unknown : boolean = false;
  rt_unknown : boolean = false;

  if memop == MemOp_LOAD & wback & n == t & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_WBSUPPRESS  => wback = false     (* writeback is suppressed *)
      Constraint_UNKNOWN  =>    wb_unknown = true (* writeback is UNKNOWN *)
      Constraint_UNDEF  =>      UnallocatedEncoding()
      Constraint_NOP  =>        EndOfInstruction()
    };*/
  };

  if memop == MemOp_STORE & wback & n == t & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_NONE  =>    rt_unknown = false (* value stored is original value *)
      Constraint_UNKNOWN  => rt_unknown = true  (* value stored is UNKNOWN *)
      Constraint_UNDEF  =>   UnallocatedEncoding()
      Constraint_NOP  =>     EndOfInstruction()
    };*/
  };

  if n == 31 then {
    if memop != MemOp_PREFETCH then CheckSPAlignment();
    address = rSP();
  } else
    address = rX(n);

  if ~(postindex) then
    address = address + offset;

  if memop == MemOp_STORE then
    /* anounce the address */
    wMem_Addr(address, quot (datasize,8), acctype, false);

  /* this is a hack to allow the address write back to be observed
     before the memory access */
  if wback then {
    let address' = (if ~(postindex) then address else (address + offset)) : bits(64) in
    if n == 31 then
      wSP() = address'
    else
      wX(n) = address'
  };

  match memop {
    MemOp_STORE  => {
      if rt_unknown then
        data = UNKNOWN : bits('D)
      else
        data = rX(t);

      flush_write_buffer(
        wMem(empty_write_buffer, address, quot(datasize,8), acctype, data)
      );
    },

    MemOp_LOAD  => {
      data = flush_read_buffer(
        rMem(empty_read_buffer, address, quot(datasize,8), acctype),
        quot(datasize,8)
      );
      if _signed then
        wX(t) = SignExtend(data) : bits('R)
      else
        wX(t) = ZeroExtend(data) : bits('R);
    },

    MemOp_PREFETCH  =>
      Prefetch(address,t : bits(5))
  };

/* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address = (bits(64)) UNKNOWN
    else if postindex then
      address = address + offset;
    if n == 31 then
      wSP() = address
    else
      wX(n) = address;
  };
*/
}

/* LDTR/STTR */
/* LDTRB/STTRB */
/* LDTRH/STTRH */
/* LDTRSB */
/* LDTRSH */
/* LDTRSW */

val decodeLoadStoreRegisterUnprivileged : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterUnprivileged (size@0b111@[0]@0b00@opc@[0]@(imm9 : bits(9))@0b10@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : uinteger = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_UNPRIV,false);
}

/* LDUR/STRUR */
/* LDURB/STURB */
/* LDURH/STURH */
/* LDURSB */
/* LDURSH */
/* LDURSW */
/* PRFUM */
val decodeLoadStoreRegisterUnscaledImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterUnscaledImmediate (size@0b111@[0]@0b00@opc@[0]@(imm9 : bits(9))@0b00@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : uinteger = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,true);
}

/* LDR/STR (immediate) Unsigned offset */
/* LDRB/STRB (immediate) Unsigned offset */
/* LDRH/STRH (immediate) Unsigned offset */
/* LDRSB (immediate) Unsigned offset */
/* LDRSH (immediate) Unsigned offset */
/* LDRSW (immediate) Unsigned offset */
/* PRFM (immediate) Unsigned offset */
val decodeLoadStoreRegisterUnsignedImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterUnsignedImmediate (size@0b111@[0]@0b01@opc@(imm12 : bits(12))@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : uinteger = UInt(size);
  offset : bits(64) = LSL(ZeroExtend(imm12), scale);

  sharedDecodeLoadImmediate(opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,true);
}

function sharedDecodeLoadStorePair forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        (L,opc : bits(2),imm7,Rn,Rt,Rt2,wback,postindex) -> option(ast('R,'D)) = {
  n : (reg_index) = UInt_reg(Rn);
  t : (reg_index) = UInt_reg(Rt);
  t2 : (reg_index) = UInt_reg(Rt2);
  acctype : (AccType) = AccType_NORMAL;
  memop : (MemOp) = if L == 1 then MemOp_LOAD else MemOp_STORE;
  if [L,opc[0]] == 0b01 | opc == 0b11 then UnallocatedEncoding();
  _signed : (boolean) = (opc[0] != 0);
  scale : (uinteger) = 2 + UInt([opc[1]]);
  datasize : atom('D) = lsl(8, scale);
  offset : (bits(64)) = LSL(SignExtend(imm7), scale);

  Some(LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize,offset));
}

/* LDP signed offset */
/* LDPSW signed offset */
/* STP signed offset */
val decodeLoadStoreRegisterPairOffset : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterPairOffset (opc@0b101@[0]@0b010@[L]@(imm7 : bits(7))@Rt2@Rn@Rt) = {
  wback : boolean = false;
  postindex : boolean = false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

function clause execute ( LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize : atom('D),offset) ) = {
  address : bits(64) = 0; /* ARM: uninitialized */
  data1 : (bits('D)) = 0; /* ARM: uninitialized */
  data2 : (bits('D)) = 0; /* ARM: uninitialized */
  /*constant*/ dbytes : (uinteger) = quot (datasize,8);
  rt_unknown : (boolean) = false;
  wb_unknown : (boolean) = false;

  if memop == MemOp_LOAD & wback & (t == n | t2 == n) & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_WBSUPPRESS, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_WBSUPPRESS  => wback = false     (* writeback is suppressed *)
      Constraint_UNKNOWN  =>    wb_unknown = true, (* writeback is UNKNOWN *)
      Constraint_UNDEF  =>      UnallocatedEncoding(),
      Constraint_NOP  =>        EndOfInstruction()
    };*/
  };

  if memop == MemOp_STORE & wback & (t == n | t2 == n) & n != 31 then {
    UnallocatedEncoding(); /* ARM:
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_NONE  =>    rt_unknown = false (* value stored is pre-writeback *)
      Constraint_UNKNOWN  => rt_unknown = true  (* value stored is UNKNOWN *)
        Constraint_UNDEF  =>   UnallocatedEncoding()
        Constraint_NOP  =>     EndOfInstruction()
    };*/
  };

  if memop == MemOp_LOAD & t == t2 then {
    UnallocatedEncoding(); /* ARM
    Constraint c = ConstrainUnpredictable();
    assert( c vIN [Constraint_UNKNOWN, Constraint_UNDEF, Constraint_NOP] );
    switch c {
      Constraint_UNKNOWN  => rt_unknown = true (* result is UNKNOWN *)
      Constraint_UNDEF  =>   UnallocatedEncoding()
      Constraint_NOP  =>     EndOfInstruction()
    };*/
  };

  if n == 31 then {
    CheckSPAlignment();
    address = rSP();
  } else
    address = rX(n);

  if ~(postindex) then
    address = address + offset;

  if memop == MemOp_STORE then
    /* anounce the address */
    wMem_Addr(address, dbytes * 2, acctype, false);

  /* this is a hack to allow the address write back to be observed
     before the memory access */
  if wback then {
    let address' = (if ~(postindex) then address else (address + offset)) : (bits(64)) in
    if n == 31 then
      wSP() = address'
    else
      wX(n) = address'
  };

  match memop {
    MemOp_STORE  => {
      if rt_unknown & t == n then
        data1 = UNKNOWN : (bits('D))
      else
        data1 = rX(t);
      if rt_unknown & t2 == n then
        data2 = UNKNOWN : (bits('D))
      else
        data2 = rX(t2);

      write_buffer : write_buffer_type = wMem(empty_write_buffer, address + 0,      dbytes, acctype, data1);
                          write_buffer = wMem(write_buffer,       address + dbytes, dbytes, acctype, data2);
      flush_write_buffer(write_buffer);
    },

    MemOp_LOAD  => {
      read_buffer : read_buffer_type = rMem(empty_read_buffer, address + 0, dbytes, acctype);
                         read_buffer = rMem(read_buffer,       address + dbytes, dbytes, acctype);
      read_data : bits('D*2) = flush_read_buffer(read_buffer, dbytes*2);
      data1 = read_data[(datasize - 1) .. 0];
      data2 = read_data[((datasize * 2) - 1) .. datasize];
      if rt_unknown then {
        data1 = UNKNOWN : bits('D);
        data2 = UNKNOWN : bits('D);
      };
      if _signed then {
        wX(t)  = (SignExtend(data1)) : (bits(64));
        wX(t2) = (SignExtend(data2)) : (bits(64));
      } else {
        wX(t)  = data1;
        wX(t2) = data2;
      };
    }
  };

/* ARM: the following code was moved up, see note there
  if wback then {
    if wb_unknown then
      address = (bits(64)) UNKNOWN
    else if postindex then
      address = address + offset;
    if n == 31 then
      wSP() = address
    else
      wX(n) = address;
  };
*/
}

/* LDP post-index */
/* LDPSW post-index */
/* STP post-index */
val decodeLoadStoreRegisterPairPostIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterPairPostIndexed (opc@0b101@[0]@0b001@[L]@(imm7 : bits(7))@Rt2@Rn@Rt) = {
  wback : boolean = true;
  postindex : boolean = true;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

/* LDP pre-index */
/* LDPSW pre-index */
/* STP pre-index */
val decodeLoadStoreRegisterPairPreIndexed : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadStoreRegisterPairPreIndexed (opc@0b101@[0]@0b011@[L]@(imm7 : bits(7))@Rt2@Rn@Rt) = {
  wback : boolean = true;
  postindex : boolean = false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

/* ADD/ADDS (immediate) */
/* SUB/SUBS (immediate) */
val decodeAddSubtractImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeAddSubtractImmediate ([sf]@[op]@[S]@0b10001@shift@(imm12 : bits(12))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  sub_op : (boolean) = (op == 1);
  setflags : (boolean) = (S == 1);
  imm : (bits('R)) = 0; /* ARM: uninitialized */

  match shift {
    0b00  => imm = ZeroExtend(imm12),
    0b01  => imm = ZeroExtend(imm12 @ (0b0 ^^ 12)),
    [1,_]  => ReservedValue()
  };

  Some(AddSubImmediate(d,n,datasize,sub_op,setflags,imm));
}

function clause execute (AddSubImmediate(d,n,datasize,sub_op,setflags,imm)) = {
  operand1 : (bits('R)) = if n == 31 then rSP() else rX(n);
  operand2 : (bits('R)) = imm;
  carry_in : (bit) = 0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = 1;
  }
  else
    carry_in = 0;

  let (result,nzcv) = AddWithCarry (operand1, operand2, carry_in) in {

    if setflags then
      wPSTATE_NZCV() = nzcv;

    if (d == 31 & ~(setflags)) then
      wSP() = result
    else
      wX(d) = result;
  }
}

/* BFM */ 
/* SBFM */
/* UBFM */
val decodeBitfield : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeBitfield ([sf]@opc@0b100110@[N]@(immr : bits(6))@(imms : bits(6))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  datasize : atom('R) = if sf == 1 then 64 else 32;

  inzero : (boolean) = false; /* ARM: uninitialized */
  extend : (boolean) = false; /* ARM: uninitialized */
  R : (uinteger) = 0; /* ARM: uninitialized */
  S : (uinteger) = 0; /* ARM: uninitialized */

  match opc {
    0b00  => {inzero = true; extend = true},   /* SBFM */
    0b01  => {inzero = false; extend = false}, /* BFM */
    0b10  => {inzero = true; extend = false},  /* UBFM */
    0b11  => UnallocatedEncoding()
  };

  if sf == 1 & N != 1 then ReservedValue();
  if sf == 0 & (N != 0 | immr[5] != 0 | imms[5] != 0) then ReservedValue();

  R = UInt(immr);
  S = UInt(imms);

  let (wmask : bits('R), tmask : bits('R)) = (DecodeBitMasks(N, imms, immr, false)) in {

  Some(BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask));
}}


function clause execute (BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask)) = {
  dst : bits('R) = if inzero then Zeros() else rX(d);
  src : bits('R) = rX(n);

  /* perform bitfield move on low bits */
  bot : (bits('R)) = ((dst & NOT(wmask)) | (ROR(src, R) & wmask));

  /* determine extension bits (sign, zero or dest register) */
  top : (bits('R)) = if extend then Replicate([src[S]]) else dst;

  /* combine extension bits and result bits */
  wX(d) = ((top & NOT(tmask)) | (bot & tmask));
}

/* EXTR */
val decodeExtract : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeExtract ([sf]@0b00@0b100111@[N]@0b0@Rm@(imms : bits(6))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  lsb : (uinteger) = 0; /* ARM: uninitialized */

  if N != sf then UnallocatedEncoding();
  if sf == 0 & imms[5] == 1 then ReservedValue();
  lsb = UInt(imms);

  Some(ExtractRegister(d,n,m,datasize,lsb));
}

function clause execute ( ExtractRegister(d,n,m,datasize : atom('R),lsb) ) = {
  result : (bits('R)) = 0; /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  concat : (bits(2*'R)) = operand1:operand2;
  result = concat[(lsb + datasize - 1)..lsb];
  wX(d) = result;
}

/* AND/ANDS (immediate) */
/* EOR (immediate) */
/* ORR (immediate) */
val decodeLogicalImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLogicalImmediate ([sf]@opc@0b100100@[N]@(immr : bits(6))@(imms : bits(6))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  setflags : (boolean) = false; /* ARM: uninitialized */
  op : (LogicalOp) = LogicalOp_AND; /* ARM: uninitialized */
  match opc {
    0b00  => {op = LogicalOp_AND; setflags = false},
    0b01  => {op = LogicalOp_ORR; setflags = false},
    0b10  => {op = LogicalOp_EOR; setflags = false},
    0b11  => {op = LogicalOp_AND; setflags = true}
  };

  if sf == 0 & N != 0 then ReservedValue();
  let (imm,_) = (DecodeBitMasks(N, imms, immr, true)) in {

  Some(LogicalImmediate(d,n,datasize,setflags,op,imm));
}}

function clause execute (LogicalImmediate(d,n,datasize : atom('R),setflags,op,imm)) = {
  result : (bits('R)) = 0; /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = imm;

  match op {
    LogicalOp_AND  => result = (operand1 & operand2),
    LogicalOp_ORR  => result = (operand1 | operand2),
    LogicalOp_EOR  => result = (operand1 ^ operand2)
  };

  if setflags then
    wPSTATE_NZCV() = ([result[length(result) - 1]]@[IsZeroBit(result)]@0b00);

  if d == 31 & ~(setflags) then
    wSP() = result
  else
    wX(d) = result;
}

/* MOVK */
/* MOVN */
/* MOVZ */
val decodeMoveWideImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeMoveWideImmediate ([sf]@opc@0b100101@(hw : bits(2))@(imm16 : bits(16))@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  imm : (bits(16)) = imm16;
  pos : (uinteger) = 0; /* ARM: uninitialized */
  opcode : (MoveWideOp) = 0; /* ARM: uninitialized */

  match opc {
    0b00  => opcode = MoveWideOp_N,
    0b10  => opcode = MoveWideOp_Z,
    0b11  => opcode = MoveWideOp_K,
    _  => UnallocatedEncoding()
  };

  if sf == 0 & hw[1] == 1 then UnallocatedEncoding();
  pos = UInt(hw@0b0000);

  Some(MoveWide(d,datasize,imm,pos,opcode));
}

function clause execute ( MoveWide(d,datasize,imm,pos,opcode) ) = {
  result : (bits('R)) = 0; /* ARM: uninitialized */

  if opcode == MoveWideOp_K then
    result = rX(d)
  else
    result = Zeros();

  result[(pos+15)..pos] = imm;
  if opcode == MoveWideOp_N then
    result = NOT(result);
  wX(d) = result;
}

/* ADR */
/* ADRP */
val decodePCRelAddressing : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodePCRelAddressing ([op]@(immlo : bits(2))@0b10000@(immhi : bits(19))@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  page : (boolean) = (op == 1);
  imm :(bits(64)) = 0; /* ARM: uninitialized */

  if page then
    imm = SignExtend(immhi@immlo@(0b0 ^^ 12))
  else
    imm = SignExtend(immhi@immlo);

  Some(Address(d,page,imm))
}

function clause execute (Address(d,page,imm)) = {
  base : (bits(64)) = rPC();

  if page then
    base[11..0] = (Zeros()) @ (bits(12));

  wX(d) = base + imm;
}

/* ADD/ADDS (extended register) */
/* SUB/SUBS (extended register) */
val decodeAddSubtractExtendedRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeAddSubtractExtendedRegister ([sf]@[op]@[S]@0b01011@0b00@0b1@Rm@option_v@(imm3 : bits(3))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  sub_op : (boolean) = (op == 1);
  setflags : (boolean) = (S == 1);
  extend_type : (ExtendType) = DecodeRegExtend(option_v);
  shift : range(0,7) = UInt(imm3);
  if shift > 4 then ReservedValue();

  Some(AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift));
}

function clause execute (AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift)) = {
  operand1 : (bits('R)) = if n == 31 then rSP() else rX(n);
  operand2 : (bits('R)) = ExtendReg(m, extend_type, shift);
  carry_in : (bit) = 0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = 1;
  } else
    carry_in = 0;

  let (result,nzcv) = (AddWithCarry(operand1, operand2, carry_in)) in {

    if setflags then
      wPSTATE_NZCV() = nzcv;

    if (d == 31 & ~(setflags)) then
      wSP() = result
    else
      wX(d) = result;
  }
}

/* ADD/ADDS (shifted register) */
/* SUB/SUBS (shifted register) */
val decodeAddSubtractShiftedRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeAddSubtractShiftedRegister ([sf]@[op]@[S]@0b01011@shift@0b0@Rm@(imm6 : bits(6))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  sub_op : (boolean) = (op == 1);
  setflags : (boolean) = (S == 1);

  if shift == 0b11 then ReservedValue();
  if sf == 0 & imm6[5] == 1 then ReservedValue();

  shift_type : (ShiftType) = DecodeShift(shift);
  shift_amount : range(0,63) = UInt(imm6);

  Some(AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount));
}

function clause execute (AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount)) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = ShiftReg(m, shift_type, shift_amount);
  carry_in : (bit) = 0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = 1;
  }
  else
    carry_in = 0;

  let (result,nzcv) = AddWithCarry(operand1, operand2, carry_in) in {

    if setflags then
      wPSTATE_NZCV() = nzcv;

    wX(d) = result;
  }
}

/* ADC/ADCS */
/* SBC/SBCS */


val decodeAddSubtractWithCarry : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeAddSubtractWithCarry ([sf]@[op]@[S]@0b11010000@Rm@0b000000@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  sub_op : (boolean) = (op == 1);
  setflags : (boolean) = (S == 1);

  Some(AddSubCarry(d,n,m,datasize,sub_op,setflags));
}

function clause execute( AddSubCarry(d,n,m,datasize,sub_op,setflags)) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  if sub_op then
    operand2 = NOT(operand2);

  let (result,nzcv) = AddWithCarry (operand1, operand2, PSTATE_C) in {

  if setflags then
    wPSTATE_NZCV() = nzcv;

  wX(d) = result;
}}

/* CCMN (immediate) */
/* CCMP (immediate) */
val decodeConditionalCompareImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeConditionalCompareImmediate ([sf]@[op]@[1]@0b11010010@(imm5 : bits(5))@ _cond@[1]@[0]@Rn@[0]@nzcv) = {
  n : (reg_index) = UInt_reg(Rn);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  sub_op : boolean = (op ==1);
  condition : bits(4) = _cond;
  flags : bits(4) = nzcv;
  imm : bits('R) = ZeroExtend(imm5);

  Some(ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm));
}

function clause execute (ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm)) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = imm;
  carry_in : (bit) = 0;

  flags' : (bits(4)) = flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = NOT(operand2);
      carry_in = 1;
    };
    let (_,nzcv) =  AddWithCarry(operand1, operand2, carry_in) in {flags' = nzcv};
  };
  wPSTATE_NZCV() = flags';
}

/* CCMN (register) */
/* CCMP (register) */
val decodeConditionalCompareRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeConditionalCompareRegister ([sf]@[op]@[1]@0b11010010@Rm@ _cond@[0]@[0]@Rn@[0]@nzcv) = {
  n : reg_index = UInt_reg(Rn);
  m : reg_index = UInt_reg(Rm);
  datasize : atom('R) = if sf == 1 then 64 else 32;
  sub_op : boolean = (op ==1);
  condition : bits(4) = _cond;
  flags : bits(4) = nzcv;

  Some(ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags));
}

function clause execute (ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags)) = {
  operand1 : bits('R) = rX(n);
  operand2 : bits('R) = rX(m);
  carry_in : bit = 0;

  flags' : bits(4) = flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = NOT(operand2);
      carry_in = 1;
    };
    let (_,nzcv) = AddWithCarry (operand1, operand2, carry_in) in {flags' = nzcv};
  };
  wPSTATE_NZCV() = flags';
}

/* CSEL op=0,o2=0 */
/* CSINC op=0,o2=1 */
/* CSINV op=1,o2=0 */
/* CSNEG op=1,o2=1 */
val decodeConditionalSelect : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeConditionalSelect ([sf]@[op]@[0]@0b11010100@Rm@ _cond@[0]@[o2]@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  condition : (bits(4)) = _cond;
  else_inv : (boolean) = (op == 1);
  else_inc : (boolean) = (o2 == 1);

  Some(ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc));
}

function clause execute ( ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc) ) = {
  result : (bits('R)) = 0; /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  if ConditionHolds(condition) then
    result = operand1
  else {
    result = operand2;
    if else_inv then result = NOT(result);
    if else_inc then result = result + 1;
  };

  wX(d) = result;
}

val decodeData1Source : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
scattered function decodeData1Source

/* RBIT */
/* REV */
/* REV16 */
/* REV32 */
function clause decodeData1Source ([sf]@[1]@[0]@0b11010110@0b00000@0b0000@opc@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);

  datasize : (atom('R)) = if sf == 1 then 64 else 32;

  op : (RevOp) = 0; /* ARM: uninitialized */
  match opc {
    0b00  =>
      op = RevOp_RBIT,
    0b01  =>
      op = RevOp_REV16,
    0b10  =>
      op = RevOp_REV32,
    0b11  => {
      if sf == 0 then UnallocatedEncoding();
      op = RevOp_REV64;
    }
  };

  Some(Reverse(d,n,datasize,op));
}

function clause execute ( Reverse(d,n,datasize,op) ) = {
  result : (bits('R)) = 0; /* ARM uninitialized */
  V : (bits(6)) = 0; /* ARM uninitialized */

  match op {
    RevOp_REV16  => V = 0b001000,
    RevOp_REV32  => V = 0b011000,
    RevOp_REV64  => V = 0b111000,
    RevOp_RBIT  =>  V = if datasize == 64 then 0b111111 else 0b011111
  };

  result = rX(n);

  foreach (vbit from 0 to 5) {
    /* Swap pairs of 2^vbit bits in result */
    if V[vbit] == 1 then {
      tmp : (bits('R)) = result;
      vsize : (uinteger) = lsl(1, vbit);
      foreach (base from 0 to (datasize - 1) by (2 * vsize)) { /* ARM: while base < datasize do */
        result[((base+vsize) - 1)..base] = tmp[(base+(2*vsize) - 1)..(base+vsize)];
        result[(base+(2*vsize) - 1)..(base+vsize)] = tmp[(base+vsize - 1)..base];
        /* ARM: base = base + (2 * vsize); */
      };
    };
  };
  wX(d) = result;
}

/* CLS */
/* CLZ */
function clause decodeData1Source ([sf]@[1]@[0]@0b11010110@0b00000@0b00010@[op]@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  opcode : (CountOp) = if op == 0 then CountOp_CLZ else CountOp_CLS;

  Some(CountLeading(d,n,datasize,opcode));
}

function clause execute (CountLeading(d,n,datasize,opcode)) = {
  result : (uinteger) = 0; /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);

  if opcode == CountOp_CLZ then
    result = CountLeadingZeroBits(operand1)
  else
    result = CountLeadingSignBits(operand1);

  wX(d) = result : bits('R);
}

end decodeData1Source

val decodeData2Source : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
scattered function decodeData2Source

/* SDIV o1=1 */
/* UDIV o1=0 */
function clause decodeData2Source ([sf]@[0]@[0]@0b11010110@Rm@0b00001@[o1]@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  _unsigned : (boolean) = (o1 == 0);

  Some(Division(d,n,m,datasize,_unsigned));
}

function clause execute ( Division(d,n,m,datasize,_unsigned) ) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);
  result : (integer) = 0; /* ARM: uninitialized */

  if IsZero(operand2) then
    result = 0
  else
    result = /* ARM: RoundTowardsZero*/ quot (_Int(operand1, _unsigned), _Int(operand2, _unsigned)); /* FIXME: does quot round towards zero? */

  wX(d) = result : (bits('R)) ; /* ARM: result[(datasize-1)..0] */
}

/* ASRV */
/* LSLV */
/* LSRV */
/* RORV */
function clause decodeData2Source ([sf]@[0]@[0]@0b11010110@Rm@0b0010@op2@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  shift_type : (ShiftType) = DecodeShift(op2);

  Some(Shift(d,n,m,datasize,shift_type));
}

function clause execute (Shift(d,n,m,datasize,shift_type)) = {
  result : (bits('R)) = 0; /* ARM: uninitialized */
  operand2 : (bits('R)) = rX(m);

  result = ShiftReg(n, shift_type, mod (UInt(operand2), datasize));
  wX(d) = result;
}

/* CRC32B/CRC32H/CRC32W/CRC32X C=0 */
/* CRC32CB/CRC32CH/CRC32CW/CRC32CX C=1 */
function clause decodeData2Source ([sf]@[0]@[0]@0b11010110@Rm@0b010@[C]@sz@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  if sf == 1 & sz != 0b11 then UnallocatedEncoding();
  if sf == 0 & sz == 0b11 then UnallocatedEncoding();
  size : (atom('D)) = lsl(8, UInt(sz)); /* 2-bit size field -> 8, 16, 32, 64 */
  crc32c : (boolean) = (C == 1);

  Some(CRC(d,n,m,size,crc32c));
}

function clause execute ( CRC(d,n,m,size,crc32c) ) = {
  if ~(HaveCRCExt()) then
    UnallocatedEncoding();

  acc : (bits(32))  = rX(n); /* accumulator */
  _val : (bits('D)) = rX(m); /* input value */
  poly : (bits(32)) = if crc32c then 0x1EDC6F41 else 0x04C11DB7;

  tempacc : (bits(32+'D)) = BitReverse(acc)  @ (Zeros(): bits('D));
  tempval : (bits('D+32)) = BitReverse(_val) @ (Zeros() : bits(32));

  /* Poly32Mod2 on a bitstring does a polynomial Modulus over {0,1} operation */
  wX(d) = BitReverse(Poly32Mod2(tempacc ^ tempval, poly));
}

end decodeData2Source

val decodeData3Source : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
scattered function decodeData3Source

/* MADD o0=0 */
/* MSUB o0=1 */
function clause decodeData3Source ([sf]@0b00@0b11011@0b000@Rm@[o0]@Ra@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  a : (reg_index) = UInt_reg(Ra);
  destsize : (atom('R)) = if sf == 1 then 64 else 32;
  datasize : (atom('D)) = destsize;
  sub_op : (boolean) = (o0 == 1);

  Some(MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op));
}

function clause execute ( MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op) ) = {
  operand1 : (bits('D)) = rX(n);
  operand2 : (bits('D)) = rX(m);
  operand3 : (bits('R)) = rX(a);

  result : (integer) = 0; /* ARM: uninitialized */

  if sub_op then
    result = UInt(operand3) - (UInt(operand1) * UInt(operand2))
  else
    result = UInt(operand3) + (UInt(operand1) * UInt(operand2));

  wX(d) = result : (bits('R));
}

/* SMADDL */
/* SMSUBL */
/* UMADDL */
/* UMSUBL */
function clause decodeData3Source ([1]@0b00@0b11011@[U]@0b01@Rm@[o0]@Ra@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  a : (reg_index) = UInt_reg(Ra);
  destsize : (atom('R)) = 64;
  datasize : (atom('D)) = 32;
  sub_op : (boolean) = (o0 == 1);
  _unsigned : (boolean) = (U == 1);

  Some(MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned));
}

function clause execute ( MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned) ) = {
  operand1 : (bits('D)) = rX(n);
  operand2 : (bits('D)) = rX(m);
  operand3 : (bits('R)) = rX(a);

  result : (integer) = 0; /* ARM: uninitialized */

  if sub_op then
    result = _Int(operand3, _unsigned) - (_Int(operand1, _unsigned) * _Int(operand2, _unsigned))
  else
    result = _Int(operand3, _unsigned) + (_Int(operand1, _unsigned) * _Int(operand2, _unsigned));

  wX(d) = result : (bits(64));
}

/* SMULH */
/* UMULH */
function clause decodeData3Source ([1]@0b00@0b11011@[U]@0b10@Rm@[0]@Ra@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  a : (reg_index) = UInt_reg(Ra); /* ignored by UMULH/SMULH */
  destsize : (atom('R)) = 64;
  datasize : (atom('D)) = destsize;
  _unsigned : (boolean) = (U == 1);

  Some(MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned));
}

function clause execute ( MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned) ) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  result : (integer) = 0; /* ARM: uninitialized */

  result = _Int(operand1, _unsigned) * _Int(operand2, _unsigned);

  wX(d) = (result : bits(128))[127..64];
}

end decodeData3Source

/* AND/ANDS (shifted register) */
/* EON (shifted register) */
/* EOR (shifted register) */
/* ORN (shifted register) */
/* ORR (shifted register) */
/* BIC/BICS (shifted register) */
val decodeLogicalShiftedRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLogicalShiftedRegister ([sf]@opc@0b01010@shift@[N]@Rm@(imm6 : bits(6))@Rn@Rd) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : (atom('R)) = if sf == 1 then 64 else 32;
  setflags : (boolean) = false; /* ARM: uninitialized */
  op : (LogicalOp) = LogicalOp_AND; /* ARM: uninitialized */
  match opc {
    0b00  => {op = LogicalOp_AND; setflags = false},
    0b01  => {op = LogicalOp_ORR; setflags = false},
    0b10  => {op = LogicalOp_EOR; setflags = false},
    0b11  => {op = LogicalOp_AND; setflags = true}
  };

  if sf == 0 & imm6[5] == 1 then ReservedValue();

  shift_type : (ShiftType) = DecodeShift(shift);
  shift_amount : range(0,63) = UInt(imm6);
  invert : (boolean) = (N == 1);

  Some(LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert))
}

function clause execute (LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert)) = {

  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = ShiftReg(m, shift_type, shift_amount);

  if invert then operand2 = NOT(operand2);

  result : (bits('R)) = 0; /* ARM: uninitialized */
  match op {
    LogicalOp_AND  => result = (operand1 & operand2),
    LogicalOp_ORR  => result = (operand1 | operand2),
    LogicalOp_EOR  => result = (operand1 ^ operand2)
  };

  if setflags then
    wPSTATE_NZCV() = ([result[datasize - 1]]@[IsZeroBit(result)]@0b00);

  wX(d) = result;
}

val decodeDataSIMDFPoint1 : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeDataSIMDFPoint1 (machineCode) = {
  not_implemented("decodeDataSIMDFPoint1");
  Some(Unallocated);
}

val decodeDataSIMDFPoint2 : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decodeDataSIMDFPoint2 ( machineCode) = {
  not_implemented("decodeDataSIMDFPoint2");
  Some(Unallocated);
}

val decodeDataRegister : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeDataRegister (machineCode) = {
  match machineCode {
    ([_]@[_]@[_]@[0]@ [1]@[0]@[1]@[0]@ [_]@[_]@[_]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeLogicalShiftedRegister(machineCode),
    ([_]@[_]@[_]@[0]@ [1]@[0]@[1]@[1]@ [_]@[_]@[0]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractShiftedRegister(machineCode),
    ([_]@[_]@[_]@[0]@ [1]@[0]@[1]@[1]@ [_]@[_]@[1]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractExtendedRegister(machineCode),
    ([_]@[_]@[_]@[1]@ [1]@[0]@[1]@[0]@ [0]@[0]@[0]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractWithCarry(machineCode),
    ([_]@[_]@[_]@[1]@ [1]@[0]@[1]@[0]@ [0]@[1]@[0]@ (_ : bits(9)) @[0]@(_ : bits(11)))  => decodeConditionalCompareRegister(machineCode),
    ([_]@[_]@[_]@[1]@ [1]@[0]@[1]@[0]@ [0]@[1]@[0]@ (_ : bits(9)) @[1]@(_ : bits(11)))  => decodeConditionalCompareImmediate(machineCode),
    ([_]@[_]@[_]@[1]@ [1]@[0]@[1]@[0]@ [1]@[0]@[0]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeConditionalSelect(machineCode),
    ([_]@[_]@[_]@[1]@ [1]@[0]@[1]@[1]@ [_]@[_]@[_]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData3Source(machineCode),
    ([_]@[0]@[_]@[1]@ [1]@[0]@[1]@[0]@ [1]@[1]@[0]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData2Source(machineCode),
    ([_]@[1]@[_]@[1]@ [1]@[0]@[1]@[0]@ [1]@[1]@[0]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData1Source(machineCode)
  }
}

val decodeDataImmediate : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeDataImmediate (machineCode) = {
  match machineCode {
    ((_ : bits(3))@[1]@[0]@[0]@[0]@[0]@[_]@(_ : bits(23)))  => decodePCRelAddressing(machineCode),
    ((_ : bits(3))@[1]@[0]@[0]@[0]@[1]@[_]@(_ : bits(23)))  => decodeAddSubtractImmediate(machineCode),
    ((_ : bits(3))@[1]@[0]@[0]@[1]@[0]@[0]@(_ : bits(23)))  => decodeLogicalImmediate(machineCode),
    ((_ : bits(3))@[1]@[0]@[0]@[1]@[0]@[1]@(_ : bits(23)))  => decodeMoveWideImmediate(machineCode),
    ((_ : bits(3))@[1]@[0]@[0]@[1]@[1]@[0]@(_ : bits(23)))  => decodeBitfield(machineCode),
    ((_ : bits(3))@[1]@[0]@[0]@[1]@[1]@[1]@(_ : bits(23)))  => decodeExtract(machineCode)
  }
}

val decodeLoadsStores : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeLoadsStores (machineCode) = {
  match machineCode {
    ([_]@[_]@[0]@[0]@ [1]@[0]@[0]@[0]@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreExclusive(machineCode),
    ([_]@[_]@[0]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadRegisterLiteral(machineCode),
    ([_]@[_]@[1]@[0]@ [1]@[_]@[0]@[0]@ [0]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreNoAllocatePairOffset(machineCode),
    ([_]@[_]@[1]@[0]@ [1]@[_]@[0]@[0]@ [1]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairPostIndexed(machineCode),
    ([_]@[_]@[1]@[0]@ [1]@[_]@[0]@[1]@ [0]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairOffset(machineCode),
    ([_]@[_]@[1]@[0]@ [1]@[_]@[0]@[1]@ [1]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairPreIndexed(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[0]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[0]@[0]@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnscaledImmediate(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[0]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[0]@[1]@ (_ : bits(10)) )  => decodeLoadStoreRegisterImmediatePostIndexed(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[0]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[1]@[0]@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnprivileged(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[0]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[1]@[1]@ (_ : bits(10)) )  => decodeLoadStoreRegisterImmediatePreIndexed(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[0]@ [_]@[_]@[1]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[1]@[0]@ (_ : bits(10)) )  => decodeLoadStoreRegisterRegisterOffset(machineCode),
    ([_]@[_]@[1]@[1]@ [1]@[_]@[0]@[1]@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnsignedImmediate(machineCode),
    ([0]@[_]@[0]@[0]@ [1]@[1]@[0]@[0]@ [0]@[_]@[0]@[0]@ [0]@[0]@[0]@[0]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreMultiStruct(machineCode),
    ([0]@[_]@[0]@[0]@ [1]@[1]@[0]@[0]@ [1]@[_]@[0]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreMultiStructPostIndexed(machineCode),
    ([0]@[_]@[0]@[0]@ [1]@[1]@[0]@[1]@ [0]@[_]@[_]@[0]@ [0]@[0]@[0]@[0]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreSingleStruct(machineCode),
    ([0]@[_]@[0]@[0]@ [1]@[1]@[0]@[1]@ [1]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreSingleStructPostIndexed(machineCode)
  }
}

val decodeSystemImplementationDefined : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeSystemImplementationDefined (machineCode) = {
  match machineCode {
    ((_ : bits(11)) @[0]@[1]@[_]@[_]@[_]@[1]@[_]@[1]@[1]@(_ : bits(12)))  => decodeImplementationDefined(machineCode),
    ((_ : bits(11)) @[1]@[1]@[_]@[_]@[_]@[1]@[_]@[1]@[1]@(_ : bits(12)))  => decodeImplementationDefined(machineCode),
    ((_ : bits(11)) @[_]@[_]@[_]@[_]@[_]@[_]@[_]@[_]@[_]@(_ : bits(12)))  => decodeSystem(machineCode)
  }
}


val decodeBranchesExceptionSystem : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect pure
function decodeBranchesExceptionSystem (machineCode) = {
  match machineCode {
    ([_]@[0]@[0]@[1]@[0]@[1]@[_]@[_]@[_]@[_]@(_ : bits(22)))  => decodeUnconditionalBranchImmediate(machineCode),
    ([_]@[0]@[1]@[1]@[0]@[1]@[0]@[_]@[_]@[_]@(_ : bits(22)))  => decodeCompareBranchImmediate(machineCode),
    ([_]@[0]@[1]@[1]@[0]@[1]@[1]@[_]@[_]@[_]@(_ : bits(22)))  => decodeTestBranchImmediate(machineCode),
    ([0]@[1]@[0]@[1]@[0]@[1]@[0]@[_]@[_]@[_]@(_ : bits(22)))  => decodeConditionalBranchImmediate(machineCode),
    ([1]@[1]@[0]@[1]@[0]@[1]@[0]@[0]@[_]@[_]@(_ : bits(22)))  => decodeExceptionGeneration(machineCode),
    ([1]@[1]@[0]@[1]@[0]@[1]@[0]@[1]@[0]@[0]@(_ : bits(22)))  => decodeSystemImplementationDefined(machineCode),
    ([1]@[1]@[0]@[1]@[0]@[1]@[1]@[_]@[_]@[_]@(_ : bits(22)))  => decodeUnconditionalBranchRegister(machineCode)
  }
}

val decode : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}.
        bits(32) -> option(ast('R,'D)) effect {escape}
function decode (machineCode) = {
  match machineCode {
    ((_ : bits(3)) @[0]@[0]@[_]@[_]@(_ : bits(25)))  => Some(Unallocated),
    ((_ : bits(3)) @[1]@[0]@[0]@[_]@(_ : bits(25)))  => decodeDataImmediate(machineCode),
    ((_ : bits(3)) @[1]@[0]@[1]@[_]@(_ : bits(25)))  => decodeBranchesExceptionSystem(machineCode),
    ((_ : bits(3)) @[_]@[1]@[_]@[0]@(_ : bits(25)))  => decodeLoadsStores(machineCode),
    ((_ : bits(3)) @[_]@[1]@[0]@[1]@(_ : bits(25)))  => decodeDataRegister(machineCode),
    ((_ : bits(3)) @[0]@[1]@[1]@[1]@(_ : bits(25)))  => decodeDataSIMDFPoint1(machineCode),
    ((_ : bits(3)) @[1]@[1]@[1]@[1]@(_ : bits(25)))  => decodeDataSIMDFPoint2(machineCode),
    _                                                => None
  }
}
    
end execute

val supported_instructions : forall 'R 'D, 'R in {32,64} & 'D in {8,16,32,64}. ast('R,'D) -> option(ast('R,'D)) effect pure
function supported_instructions (instr) = {
  match instr {
    _  => Some(instr)
  }
}
