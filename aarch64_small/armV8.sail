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


type RegisterSize('R: Int) -> Bool = 'R in {32, 64}
type DataSize('D: Int) -> Bool = 'D in {8, 16, 32, 64}

union ast =  {
  Unallocated : unit,
  ImplementationDefinedTestBeginEnd : boolean,
  ImplementationDefinedStopFetching : unit,
  ImplementationDefinedThreadStart : unit,

  /* transactional memory, not part of the official spec */
  TMStart : reg_index,
  TMCommit : unit,
  TMAbort : (boolean,bits(5)),
  TMTest : unit,

  CompareAndBranch : {'R, RegisterSize('R). (reg_index, int('R), boolean, bits(64))},
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
  DataCache : (reg_index,DCOp),
  InstructionCache : (reg_index,ICOp),
  MoveSystemRegister : (reg_index,uinteger,uinteger,uinteger,uinteger,uinteger,boolean),
  TestBitAndBranch : {'R 'bit_pos, RegisterSize('R) & 0 <= 'bit_pos < 'R. (reg_index,int('R),int('bit_pos),bit,bits(64))},
  BranchImmediate : (BranchType,bits(64)),
  BranchRegister : (reg_index,BranchType),
  ExceptionReturn : unit, /* TODO: add to .hgen */
  DebugRestorePState : unit, /* TODO: add to .hgen */
  LoadLiteral : {'D 'size, RegisterSize('D) & 'size in {1,2,4,8/* ,16 */} & 'size * 8 == 'D. (reg_index,MemOp,boolean,int('size),bits(64),int('D))},
  LoadStoreAcqExc : {'D 'R 'elsize, 'D in {8, 16, 32, 64, 128} & RegisterSize('R) & 'elsize <= 'D. (reg_index,reg_index,reg_index,reg_index,AccType,boolean,boolean,MemOp,int('elsize),int('R),int('D))},
  LoadStorePairNonTemp : {'D, DataSize('D). (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,uinteger,int('D),bits(64))},
  LoadImmediate : {'D 'R, DataSize('D) & RegisterSize('R). (reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,bits(64),int('R),int('D))},
  LoadRegister : {'D 'R, DataSize('D) & RegisterSize('R). (reg_index,reg_index,reg_index,AccType,MemOp,boolean,boolean,boolean,ExtendType,range(0,3),int('R),int('D))},
  LoadStorePair : {'D, DataSize('D). (boolean,boolean,reg_index,reg_index,reg_index,AccType,MemOp,boolean,int('D),bits(64))},
  AddSubImmediate : {'R, RegisterSize('R). (reg_index,reg_index,int('R),boolean,boolean,bits('R))},
  BitfieldMove : {'R 'r 's, RegisterSize('R) & 0 <= 'r < 'R & 0 <= 's < 'R. (reg_index,reg_index,int('R),boolean,boolean,int('r),int('s),bits('R),bits('R))},
  ExtractRegister : {'R 'lsb, RegisterSize('R) & 0 <= 'lsb <= 'R. (reg_index,reg_index,reg_index,int('R),int('lsb))},
  LogicalImmediate : {'R, RegisterSize('R). (reg_index,reg_index,int('R),boolean,LogicalOp,bits('R))},
  MoveWide : {'R 'pos, RegisterSize('R) & 0 <= 'pos < div('R, 2). (reg_index,int('R),bits(16),int('pos),MoveWideOp)},
  Address : (reg_index,boolean,bits(64)),
  AddSubExtendRegister : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),boolean,boolean,ExtendType,range(0,7))},
  AddSubShiftedRegister : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),boolean,boolean,ShiftType,range(0,63))},
  AddSubCarry : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),boolean,boolean)},
  ConditionalCompareImmediate : {'R, RegisterSize('R). (reg_index,int('R),boolean,bits(4),bits(4),bits('R))},
  ConditionalCompareRegister : {'R, RegisterSize('R). (reg_index,reg_index,int('R),boolean,bits(4),bits(4))},
  ConditionalSelect : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),bits(4),boolean,boolean)},
  Reverse : {'R, RegisterSize('R). (reg_index,reg_index,int('R),RevOp)},
  CountLeading : {'R, RegisterSize('R). (reg_index,reg_index,int('R),CountOp)},
  Division : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),boolean)},
  Shift : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),ShiftType)},
  CRC : {'D, DataSize('D). (reg_index,reg_index,reg_index,int('D),boolean)},
  MultiplyAddSub : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,reg_index,int('R),int('R),boolean)},
  MultiplyAddSubLong : {'D 'R, DataSize('D) & RegisterSize('R). (reg_index,reg_index,reg_index,reg_index,int('R),int('D),boolean,boolean)},
  MultiplyHigh : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,reg_index,int('R),int('R),boolean)},
  LogicalShiftedRegister : {'R, RegisterSize('R). (reg_index,reg_index,reg_index,int('R),boolean,LogicalOp,ShiftType,range(0,63),boolean)},
}

val execute : ast -> unit effect {rreg,wreg,rmem,barr,eamem,wmv,exmem,escape}
scattered function execute

/* TSTART - dummy decoding */
val decodeTMStart : bits(5) -> option (ast)
function decodeTMStart (Rt) = {
  t : reg_index = UInt_reg(Rt);
  Some(TMStart(t));
}

/* transactional memory, not part of the official spec */
function clause execute (TMStart(t)) = {
  nesting : bits(8) = TxNestingLevel;

  if nesting <_u TXIDR_EL0.DEPTH() then {
    TxNestingLevel = nesting + 1;
    status : bits(64) = Zeros();
    if nesting == 0b00000000 then
      status = TMStartEffect.bits(); /* fake effect */
    wX(t) = status;
  } else {
    status : bits(64) = Zeros();
    status[10] = b1; /* set the NEST bit */
    TMAbortEffect->bits() = status; /* fake effect */
  }
}

/* external */ val "TMCommitEffect" : unit -> unit effect {barr}

/* TCOMMIT - dummy decoding */
val decodeTMCommit : unit -> option(ast) effect pure
function decodeTMCommit () =
  Some(TMCommit())


/* transactional memory, not part of the official spec */
function clause execute (TMCommit()) = {
  nesting : bits(8) = TxNestingLevel;

  if nesting == 0b00000001 then
    TMCommitEffect() /* fake effect */
  else if nesting == 0b00000000 then
    AArch64_UndefinedFault();

  TxNestingLevel = nesting - 1;
}

/* TTEST - dummy decoding */
val decodeTMTest : unit -> option(ast) effect pure 
function decodeTMTest () = 
  Some(TMTest())


/* transactional memory, not part of the official spec */
function clause execute (TMTest()) = {
  if 0b00000000 <_u TxNestingLevel then
    wPSTATE_NZCV() = 0b0000
  else
    wPSTATE_NZCV() = 0b0100
}

/* TABORT - dummy decoding */
val decodeTMAbort : bits(6) -> option(ast) effect pure 
function decodeTMAbort ([R] @ (imm5 : bits(5))) = {
  Some(TMAbort(R,imm5));
}

/* transactional memory, not part of the official spec */
function clause execute (TMAbort(retry,reason)) = {
  if 0b00000000 <_u TxNestingLevel then {
    status : bits(64) = Zeros();
    status[4..0] = reason; /* REASON */
    status[8] = retry; /* RTRY */
    status[9] = b1; /* ABRT */
    TMAbortEffect->bits() = status; /* fake effect */
  };
}

/* CBNZ */
/* CBZ */
val decodeCompareBranchImmediate : bits(32) -> option(ast) effect {escape}
function decodeCompareBranchImmediate ([sf]@0b011010@[op]@(imm19:bits(19))@(Rt:bits(5))) = {
  t : reg_index = UInt_reg(Rt);
  datasize : {|32,64|} = if sf == b1 then 64 else 32;
  iszero : boolean = (op == b0);
  offset : bits(64) = SignExtend(imm19@0b00);

  Some(CompareAndBranch(t,datasize,iszero,offset));
}

function clause execute (CompareAndBranch((t,(datasize as int('R)),iszero,offset))) = {
  operand1 : bits('R) = rX(datasize,t);
  if IsZero(operand1) == iszero then
    BranchTo(rPC() + offset, BranchType_JMP);
}

/* B.cond */
val decodeConditionalBranchImmediate: bits(32) -> option(ast) effect {escape}
function decodeConditionalBranchImmediate (0b0101010@0b0@(imm19 : bits(19))@0b0@(_cond : bits(4))) = {
  offset : bits(64) = SignExtend(imm19@0b00);
  condition : bits(4) = _cond;

  Some(BranchConditional(offset,condition));
}

function clause execute (BranchConditional(offset,condition)) = {
  if ConditionHolds(condition) then
    BranchTo(rPC() + offset, BranchType_JMP);
}


val decodeExceptionGeneration : bits(32) -> option(ast) effect {escape}
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
  if ~(HaveEL(EL2)) | PSTATE_EL() == EL0 | (PSTATE_EL() == EL1 & IsSecure()) then
    UnallocatedEncoding();
    /* CP: extracting bit 0 to convert from bitvector length 1 to bit */
  hvc_enable : bit = if HaveEL(EL3) then (SCR_EL3.HCE())[0] else NOT'(HCR_EL2.HCD()[0]);
  if hvc_enable == b0 then
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
  if ~(HaveEL(EL3)) | PSTATE_EL() == EL0 then
    UnallocatedEncoding();

  AArch64_CheckForSMCTrap(imm);

  if SCR_EL3.SMD() == 0b1 then
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

  Some(ExternalDebugBreakpoint());
}


function clause execute (ExternalDebugBreakpoint()) = {
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

val decodeSystem : bits(32) -> option(ast) effect {escape}
scattered function decodeSystem

/* MSR (immediate) */
function clause decodeSystem (0b1101010100@0b0@0b00@(op1 : bits(3))@0b0100@(CRm : bits(4))@(op2 : bits(3))@0b11111) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess(0b00, op1, 0b0100, CRm, op2, 0b11111, 0); */

  operand : bits(4) = CRm;
  field : PSTATEField = PSTATEField_DAIFSet; /* ARM: uninitialized */
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
      PSTATE_D() = (PSTATE_D() | [operand[3]]);
      PSTATE_A() = (PSTATE_A() | [operand[2]]);
      PSTATE_I() = (PSTATE_I() | [operand[1]]);
      PSTATE_F() = (PSTATE_F() | [operand[0]]);
    },
    PSTATEField_DAIFClr  => {
      PSTATE_D = (PSTATE_D() & [NOT'(operand[3])]);
      PSTATE_A = (PSTATE_A() & [NOT'(operand[2])]);
      PSTATE_I = (PSTATE_I() & [NOT'(operand[1])]);
      PSTATE_F = (PSTATE_F() & [NOT'(operand[0])]);
    }
  }
}

/* HINT */
function clause decodeSystem (0b1101010100@0b0@0b00@0b011@0b0010@(CRm : bits(4))@(op2 : bits(3))@0b11111) = {
  op : SystemHintOp = SystemHintOp_NOP; /* ARM: uninitialized */

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

    SystemHintOp_WFE  => /* FIXME: implement events?
    {
      if EventRegistered() then
        ClearEventRegister()
      else {
        if PSTATE_EL() == EL0 then
          AArch64_CheckForWFxTrap(EL1, true);
        if HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL() == EL0 | PSTATE_EL() == EL1) then
          AArch64_CheckForWFxTrap(EL2, true);
        if HaveEL(EL3) & PSTATE_EL() != EL3 then
          AArch64_CheckForWFxTrap(EL3, true);
        WaitForEvent();
      }
    } */ (),

    SystemHintOp_WFI  => {
      if ~(InterruptPending()) then {
        if PSTATE_EL() == EL0 then
          AArch64_CheckForWFxTrap(EL1, false);
        if HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL() == EL0 | PSTATE_EL() == EL1) then
          AArch64_CheckForWFxTrap(EL2, false);
        if HaveEL(EL3) & PSTATE_EL() != EL3 then
          AArch64_CheckForWFxTrap(EL3, false);
        WaitForInterrupt();
      };
    },

    SystemHintOp_SEV  =>
      /* FIXME: implement events?
      SendEvent() */
      (),

    SystemHintOp_SEVL  =>
      /* FIXME: implement events?
      EventRegisterSet()*/
      (),

    _  => () /* do nothing */
  }
}

/* CLREX */
function clause decodeSystem (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b010@0b11111) = {
  /* ARM: // CRm field is ignored */
  imm : uinteger = UInt(CRm); /* we need CRm for pretty printing */
  Some(ClearExclusiveMonitor(imm));
}

function clause execute (ClearExclusiveMonitor(imm)) = {
  ClearExclusiveLocal(ProcessorID());
}

/* DMB opc=0b01*/
/* DSB opc=0b00*/
/* ISB opc=0b10*/
function clause decodeSystem (0b1101010100@0b0@0b00@0b011@0b0011@(CRm : bits(4))@0b1@(opc : bits(2))@0b11111) = {
  /* TODO: according to ARM, HCR_EL2.BSU affect the domain, but the pseudo
           code doesn't show any signs of that */
  op : MemBarrierOp = MemBarrierOp_DSB; /* ARM: uninitialized */
  domain : MBReqDomain = MBReqDomain_Nonshareable; /* ARM: uninitialized */
  types : MBReqTypes = MBReqTypes_Reads; /* ARM: uninitialized */

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
/* The following are actually aliases of SYS: */
/* DC L=0b0,SysOp(op1,CRn,CRm,op2) = Sys_DC */
/* IC L=0b0,SysOp(op1,CRn,CRm,op2) = Sys_IC */
function clause decodeSystem (0b1101010100@[L]@0b01@(op1 : bits(3))@(CRn : bits(4))@(CRm : bits(4))@(op2 : bits(3))@(Rt:bits(5))) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess(0b01, op1, CRn, CRm, op2, Rt, L);*/

  t : reg_index = UInt_reg(Rt);

  sysop : SystemOp = Sys_SYS;
  if L == b0 then
    sysop = SysOp(op1,CRn,CRm,op2);

  match sysop {
    Sys_AT => not_implemented("AT"),

    Sys_DC =>
        match (op1, CRm, op2) {
          (0b000, 0b0110, 0b001) => Some(DataCache(t,IVAC)),
          (0b000, 0b0110, 0b010) => Some(DataCache(t,ISW)),
          (0b000, 0b1010, 0b010) => Some(DataCache(t,CSW)),
          (0b000, 0b1110, 0b010) => Some(DataCache(t,CISW)),
          (0b011, 0b0100, 0b001) => Some(DataCache(t,ZVA)),
          (0b011, 0b1010, 0b001) => Some(DataCache(t,CVAC)),
          (0b011, 0b1011, 0b001) => Some(DataCache(t,CVAU)),
          (0b011, 0b1110, 0b001) => Some(DataCache(t,CIVAC)),
          _ => error("should never happen")
        },

    Sys_IC =>
        match (op1, CRm, op2) {
          (0b000, 0b0001, 0b000) => Some(InstructionCache(t,IALLUIS)),
          (0b000, 0b0101, 0b000) => Some(InstructionCache(t,IALLU)),
          (0b011, 0b0101, 0b001) => Some(InstructionCache(t,IVAU)),
          _ => error("should never happen")
        },

    Sys_TLBI => not_implemented("TLBI"),

    Sys_SYS => {
      sys_op0 : uinteger = 1;
      sys_op1 : uinteger = UInt(op1);
      sys_op2 : uinteger = UInt(op2);
      sys_crn : uinteger = UInt(CRn);
      sys_crm : uinteger = UInt(CRm);
      has_result : boolean = (L == b1);

      Some(System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result));
    }
  };
}

function clause execute ( DataCache(t,dc_op) ) = {
  addr : bits(64) = rX(t);

  match dc_op {
    IVAC  => not_implemented("DC IVAC"),
    ISW   => not_implemented("DC ISW"),
    CSW   => not_implemented("DC CSW"),
    CISW  => not_implemented("DC CISW"),
    ZVA   => not_implemented("DC ZVA"),
    CVAC  => not_implemented("DC CVAC"),
    CVAU  => data_cache_operation_CVAU = addr,
    CIVAC => not_implemented("DC CIVAC")
  };
}

function clause execute ( InstructionCache(t,ic_op) ) = {
  addr : bits(64) = rX(t);

  match ic_op {
    IALLUIS => not_implemented("IC IALLUIS"),
    IALLU   => not_implemented("IC IALLU"),
    IVAU    => instruction_cache_operation_IVAU = addr
  };
}

function clause execute ( System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result) ) = {
  if has_result then
    wX(t) = SysOp_R(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    SysOp_W(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

/* MRS L=1 */
/* MSR (register) L=0 */
function clause decodeSystem (0b1101010100@[L]@0b1@[o0]@(op1 : bits(3))@(CRn : bits(4))@(CRm : bits(4))@(op2 : bits(3))@(Rt:bits(5))) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: CheckSystemAccess([0b1]:[o0], op1, CRn, CRm, op2, Rt, L); */

  t : reg_index = UInt_reg(Rt);

  sys_op0 : uinteger = 2 + UInt([o0]);
  sys_op1 : uinteger = UInt(op1);
  sys_op2 : uinteger = UInt(op2);
  sys_crn : uinteger = UInt(CRn);
  sys_crm : uinteger = UInt(CRm);
  read : boolean = (L == b1);

  Some(MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read));
}

function clause execute ( MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read) ) = {
  if read then
    wX(t) = System_Get(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2)
  else
    System_Put(sys_op0, sys_op1, sys_crn, sys_crm, sys_op2, rX(t));
}

end decodeSystem

val decodeImplementationDefined : bits(32) -> option(ast) effect pure
scattered function decodeImplementationDefined

/* instructions to signal to Sail that test begins/ends */
function clause decodeImplementationDefined (0b1101010100@0b0@0b01@0b011@0b1@[_]@0b11@0b0000@0b000@0b0000@[isEnd]) = {
  Some(ImplementationDefinedTestBeginEnd(isEnd));
}

function clause execute ( ImplementationDefinedTestBeginEnd(isEnd) ) = {
  if isEnd then
    info("test ends")
  else
    info("test begins");
}

/* instructions to signal ppcmem to stop fetching */
function clause decodeImplementationDefined (0b1101010100@0b0@0b01@0b011@0b1@[_]@0b11@0b0000@0b000@0b00010) = {
  Some(ImplementationDefinedStopFetching())
}

function clause execute ( ImplementationDefinedStopFetching() ) = {
  info("stop fetching instructions");
}

/* instructions to signal ppcmem to start a thread */
function clause decodeImplementationDefined (0b1101010100@0b0@0b01@0b011@0b1@[_]@0b11@0b0000@0b000@0b00011) = {
  Some(ImplementationDefinedThreadStart())
}

function clause execute ( ImplementationDefinedThreadStart() ) = {
  info("thread start");
}

end decodeImplementationDefined

/* TBNZ */
/* TBZ */
val decodeTestBranchImmediate : bits(32) -> option(ast) effect {escape}
function decodeTestBranchImmediate ([b5]@0b011011@[op]@(b40 : bits(5))@(imm14 : bits(14))@(Rt:bits(5))) = {
  t : reg_index = UInt_reg(Rt);
 
  let datasize : {| 32, 64 |} /* as int('R) */ = if b5 == b1 then 64 else 32;
  let bit_pos : uinteger = UInt([b5]@b40);
  bit_val : bit = op;
  offset : bits(64) = SignExtend(imm14@0b00);

  assert(bit_pos <= datasize - 1);

  Some(TestBitAndBranch((t,datasize,bit_pos,bit_val,offset)));
}

function clause execute ( TestBitAndBranch((t:reg_index,datasize as int('R),bit_pos,bit_val,offset)) ) = {

  /* assert ('R == 32 | 'R == 64); */

  let operand : bits('R) = rX(t);

  if operand[bit_pos] == bit_val then
    BranchTo(rPC() + offset, BranchType_JMP);
}

/* B */
/* BL */
val decodeUnconditionalBranchImmediate : bits(32) -> option(ast) effect {escape}
function decodeUnconditionalBranchImmediate ([op]@0b00101@(imm26 : bits(26))) = {
  branch_type : BranchType = if op == b1 then BranchType_CALL else BranchType_JMP;
  offset : bits(64) = SignExtend(imm26@0b00);

  Some(BranchImmediate(branch_type,offset));
}

function clause execute (BranchImmediate(branch_type,offset)) = {
  if branch_type == BranchType_CALL then wX(30) = rPC() + 4;

  BranchTo(rPC() + offset, branch_type);
}


val decodeUnconditionalBranchRegister : bits(32) -> option(ast) effect {escape} 
scattered function decodeUnconditionalBranchRegister

/* BLR */
/* BR */
/* RET */
function clause decodeUnconditionalBranchRegister (0b1101011@0b00@(op : bits(2))@0b11111@0b000000@(Rn : bits(5))@0b00000) = {
  n : reg_index = UInt_reg(Rn);
  branch_type : BranchType = BranchType_CALL; /* ARM: uninitialized */

  match op {
    0b00  => branch_type = BranchType_JMP,
    0b01  => branch_type = BranchType_CALL,
    0b10  => branch_type = BranchType_RET,
    _  => UnallocatedEncoding()
  };

  Some(BranchRegister(n,branch_type));
}

function clause execute (BranchRegister(n,branch_type)) = {
  /* ARM: the 'wX(30)' happens after the 'rX(n)'.
  We reorder those to allow MP+dmb.sy+blr-addr */
  if branch_type == BranchType_CALL then wX(30) = rPC() + 4;
  target : bits(64) = rX(n);

  BranchTo(target, branch_type);
}

/* ERET */
function clause decodeUnconditionalBranchRegister (0b1101011@0b0100@0b11111@0b000000@0b11111@0b00000) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: if PSTATE_EL == EL0 then UnallocatedEncoding(); */

  Some(ExceptionReturn());
}

function clause execute (ExceptionReturn()) = {
  AArch64_ExceptionReturn(rELR'(), rSPSR());
}

/* DRPS */
function clause decodeUnconditionalBranchRegister (0b1101011@0b0101@0b11111@0b000000@0b11111@0b00000) = {
  /* FIXME: we don't allow register reads in the decoding */
  /* ARM: if ~(Halted()) | PSTATE_EL == EL0 then UnallocatedEncoding(); */

  Some(DebugRestorePState());
}

function clause execute (DebugRestorePState()) = {
  DRPSInstruction();
}

end decodeUnconditionalBranchRegister

val decodeAdvSIMDLoadStoreMultiStruct : bits(32) -> option(ast) effect {escape}
function decodeAdvSIMDLoadStoreMultiStruct (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreMultiStruct");
  Some(Unallocated());
}

val decodeAdvSIMDLoadStoreMultiStructPostIndexed : bits(32) -> option(ast) effect {escape}
function decodeAdvSIMDLoadStoreMultiStructPostIndexed (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreMultiStructPostIndexed");
  Some(Unallocated());
}

val decodeAdvSIMDLoadStoreSingleStruct : bits(32) -> option(ast) effect {escape}
function decodeAdvSIMDLoadStoreSingleStruct (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreSingleStruct");
  Some(Unallocated());
}

val decodeAdvSIMDLoadStoreSingleStructPostIndexed : bits(32) -> option(ast) effect {escape}
function decodeAdvSIMDLoadStoreSingleStructPostIndexed (machineCode) = {
  not_implemented("decodeAdvSIMDLoadStoreSingleStructPostIndexed");
  Some(Unallocated());
}

/* LDR (literal) opc=0b0_ */
/* LDRSW (literal) opc=0b10 */
/* PRFM (literal) opc=0b11 */
val decodeLoadRegisterLiteral : bits(32) -> option(ast) effect {escape}
function decodeLoadRegisterLiteral ((opc : bits(2))@0b011@0b0@0b00@(imm19 : bits(19))@(Rt:bits(5))) = {
  t : reg_index = UInt_reg(Rt);
  memop : MemOp = MemOp_LOAD;
  _signed : boolean = false;
  size : {|4,8|} = 4; /* ARM: uninitialized */
  /* offset : bits(64) = Zeros(); /\* ARM: uninitialized *\/ */

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

  offset : bits(64) = SignExtend(imm19@0b00);

  /* CP: adding let bindings so typechecker has more information */
  let size = size;
  let datasize /* as int('D) */ = size*8; /* not in ARM ARM */

  Some(LoadLiteral(t,memop,_signed,size,offset,datasize));
}

function clause execute ( LoadLiteral((t,memop,_signed,size,offset,(datasize as int('D)) )) ) = {
  address : bits(64) = rPC() + offset;
  let data = Zeros(datasize); /* ARM: uninitialized */
  match memop {
    MemOp_LOAD  => {
      let data = flush_read_buffer(
        rMem(empty_read_buffer, address, size, AccType_NORMAL),
        size
      );
      if _signed then {
        assert (size <= 4); /* FIXME: CP: adding assertion so it typechecks. This could be dealt with by capturing the relation of size and _signed in the type of LoadLiteral. */
        wX(t) = SignExtend(data) : bits(64)
      }
      else
        wX(t) = data;
    },
    MemOp_PREFETCH  =>
      Prefetch(address,to_bits(t) : bits(5)),
    _ => exit()
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
val decodeLoadStoreExclusive : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreExclusive ((size : bits(2))@0b001000@[o2]@[L]@[o1]@(Rs:bits(5))@[o0]@(Rt2:bits(5))@(Rn:bits(5))@(Rt:bits(5))) = {
  let n : reg_index = UInt_reg(Rn);
  let t : reg_index = UInt_reg(Rt);
  let t2 : reg_index = UInt_reg(Rt2); /* ignored by load/store single register */
  let s : reg_index= UInt_reg(Rs);   /* ignored by all loads and store-release */

  if ([o2,o1,o0]) == 0b100 | ([o2,o1] == 0b11) then UnallocatedEncoding();
  if o1 == b1 & size[1] == b0 then UnallocatedEncoding();

  let acctype : AccType = if o0 == b1 then AccType_ORDERED else AccType_ATOMIC;
  let excl : boolean = (o2 == b0);
  let pair : boolean = (o1 == b1);
  let memop : MemOp = if L == b1 then MemOp_LOAD else MemOp_STORE;
  let size_uint as int('size) = UInt(size);
  let elsize : int(8 * (2 ^ 'size)) = lsl(8, size_uint);
  let elsize as int('elsize) = elsize;
  assert(elsize == 8 | elsize == 16 | elsize == 32 | elsize == 64); /*FIXME: CP: adding assertion to make typecheck*/

  let regsize as int('R) = if elsize == 64 then 64 else 32;
  let datasize : {'n, 'n in {8,16,32,64,128} & 'elsize <= 'n. int('n)} = if pair then elsize * 2 else elsize;

  /* lemma: pair --> datasize = 2*regsize */
  /* follows from "if o1 == 1 & size[1] == 0 then UnallocatedEncoding();" */

  Some(LoadStoreAcqExc((n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,datasize)));
}

function clause execute ( LoadStoreAcqExc((n,t,t2,s,acctype,excl,pair,memop,elsize,(regsize as int('R)),(datasize as int('D)) ))) = {
  address : bits(64) = Zeros(); /* ARM: uninitialized */
  data : bits('D) = Zeros(datasize); /* ARM: uninitialized */
  /*constant*/ dbytes : int(div('D,8)) = quot (datasize,8);
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
  status : bit = b0;
  if memop == MemOp_STORE & excl then {
    /*(bit)*/ status = if speculate_exclusive_success() then b0 else b1;
    wX(s) = ZeroExtend([status]) : bits(32);

    /* should be:
    if status == 1 then return ();
    */
  };
  if status == b1 then () else {

  if n == 31 then {
    CheckSPAlignment();
    address = rSP();
  } else if rn_unknown then
    address = UNKNOWN_BITS() : bits(64)
  else
    address = rX(n);

  match memop {
    MemOp_STORE  => {
      /* announce the address */
      wMem_Addr(address, dbytes, acctype, excl);

      if rt_unknown then { 
        assert( pair == false & datasize < 128); /* FIXME: CP adding assertion so it typechecks: this should not happen: rt_unknown apparently false in the non-pair case  */
        data = UNKNOWN_BITS(datasize) /* : bits('D) */
      }
      else if pair then {
        let halfsize : int(div('D,2)) = quot(datasize,2);
        assert( excl ); /* FIXME: CP adding assertion: in the 'pair' case datasize > 8  */
        assert(datasize > 8);
        el1 /* : bits('R) */ = rX(halfsize/* regsize */,t); /* ARM: bits(datasize / 2) see lemma in the decoding */
        el2 /* : bits('R) */ = rX(halfsize/* regsize */,t2); /* ARM: bits(datasize / 2) see lemma in the decoding */
        data = if BigEndian() then el1@el2 else el2@el1;
      } else {
        assert(datasize < 128); /* FIXME: CP adding assertion: in the non-'pair' case datasize < 128  */
        data : bits('D) = rX(t);
      };
      if excl then {
        /* store {release} exclusive register|pair (atomic) */
        status : bit = b1;
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
        assert( excl );
        if rt_unknown then {
          assert( pair == false & datasize < 128); /* FIXME: CP adding assertion so it typechecks: this should not happen: rt_unknown apparently false in the non-pair case  */
          /* ConstrainedUNPREDICTABLE case */
          wX(t) = UNKNOWN_BITS() : bits('D)
        }
        else if elsize == 32 then {
          /* 32-bit load exclusive pair (atomic) */
          data = flush_read_buffer(
            rMem_exclusive(empty_read_buffer, address, dbytes, acctype),
            dbytes
          );
          assert(datasize == 64); /* FIXME: CP adding assertion so it typechecks: in the 'pair' case elsize*2 == datasize */
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
        assert (regsize >= datasize); /* FIXME: CP adding assertion so it typechecks: in the non-'pair' case regsize >= datasize */
        wX(t) = ZeroExtend(data) : bits('R);
      };
    },
    _ => exit()
  };
  };
}

/* LDNP */
/* STNP */
val decodeLoadStoreNoAllocatePairOffset : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreNoAllocatePairOffset ((opc : bits(2))@0b101@0b0@0b000@[L]@(imm7 : bits(7))@(Rt2:bits(5))@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;

  /* Shared decode */

  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  t2 : reg_index = UInt_reg(Rt2);
  acctype : AccType = AccType_STREAM;
  memop : MemOp = if L == b1 then MemOp_LOAD else MemOp_STORE;
  if opc[0] == b1 then UnallocatedEncoding();
  let scale : {| 2, 3 |} = 2 + UInt([opc[1]]);
  let datasize /* : {| 32,64 |} */  /* as int('D) */ = lsl(8, scale);
  assert(datasize == 32 | datasize == 64); /*FIXME: CP adding assertion to make typecheck*/
  offset : bits(64) = LSL(SignExtend(imm7), scale);

  Some(LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,datasize,offset));
}

function clause execute ( LoadStorePairNonTemp((wback,postindex,n,t,t2,acctype,memop,scale,(datasize as int('D)),offset)) ) = {
  address : bits(64) = Zeros(); /* ARM: uninitialized */
  data1 : bits('D) = Zeros(); /* ARM: uninitialized */
  data2 : bits('D) = Zeros(); /* ARM: uninitialized */
  /*constant*/ dbytes : int(div('D,8)) = quot(datasize,8);
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
    /* announce the address */
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
        data1 = UNKNOWN_BITS() : bits('D)
      else
        data1 = rX(t);
      if rt_unknown & t2 == n then
        data2 = UNKNOWN_BITS() : bits('D)
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
        data1 = UNKNOWN_BITS() : bits('D);
        data2 = UNKNOWN_BITS() : bits('D);
      };
      wX(t) = data1;
      wX(t2) = data2;
    },

    _ => exit()
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

function sharedDecodeLoadImmediate (opc : bits(2),size : bits(2), Rn : bits(5), Rt : bits(5), wback : bit ,postindex : bit, scale : range(0,3), offset : bits(64), acctype : AccType,prefetchAllowed : bool) -> option(ast)
          = {
  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  /* ARM: inorder to unify the decoding acctype was moved out.
          AccType_UNPRIV for LDT* / STT* and AccType_NORMAL for the rest.
  acctype : AccType = AccType_NORMAL/AccType_UNPRIV; */
  memop : MemOp = MemOp_LOAD; /* ARM: uninitialized */
  _signed : boolean = false; /* ARM: uninitialized */
  regsize : { 'R, RegisterSize('R). int('R) } = 64; /* ARM: uninitialized */

  if opc[1] == b0 then {
    /* store or zero-extending load */
    memop = if opc[0] == b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    _signed = false;
  } else {
    if size == 0b11 then {
      /* ARM: we use the following if/else to unify the decoding */
      if prefetchAllowed then {
        memop = MemOp_PREFETCH;
        if opc[0] == b1 then UnallocatedEncoding();
      } else {
        /* no unprivileged prefetch */
        UnallocatedEncoding();
      };
    } else {
      /* sign-extending load */
      memop = MemOp_LOAD;
      if size == 0b10 & opc[0] == b1 then UnallocatedEncoding();
      regsize = if opc[0] == b1 then 32 else 64;
      _signed = true;
    };
  };

  let datasize /* : { 'D, DataSize('D). int('D) } */ = lsl(8, scale);
  assert (datasize == 8 | datasize == 16 | datasize == 32 | datasize == 64); /* FIXME: CP: adding assertion so it typechecks */

  Some(LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize));
}

/* LDR/STR (immediate) post-index */
/* LDRB/STRB (immediate) post-index */
/* LDRH/STRH (immediate) post-index */
/* LDRSB (immediate) post-index */
/* LDRSH (immediate) post-index */
/* LDRSW (immediate) post-index */
val decodeLoadStoreRegisterImmediatePostIndexed : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterImmediatePostIndexed ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b0@(imm9 : bits(9))@0b01@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = true;
  postindex : boolean = true;
  scale : range(0,3) = UInt(size);
  offset : bits(64) = SignExtend(imm9);
  sharedDecodeLoadImmediate
    (opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

function clause execute ( LoadImmediate ((n,t,acctype,memop,_signed,wback,postindex,offset,regsize as int('R),datasize as int('D))) ) = {
  address : bits(64) = Zeros(); /* ARM: uninitialized */
  data : bits('D) = Zeros(); /* ARM: uninitialized */
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
    /* announce the address */
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
        data = UNKNOWN_BITS() : bits('D)
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
      if _signed then {
        assert('R > 'D); /* FIXME: CP: adding assertion so it typechecks */
        wX(t) = SignExtend(data) : bits('R) /* ARM: regsize */
      }
      else {
        assert('R >= 'D); /* FIXME: CP: adding assertion so it typechecks */
        wX(t) = ZeroExtend(data) : bits('R); /* ARM: regsize */
      }
    },

    MemOp_PREFETCH  =>
      Prefetch(address, to_bits(t) : bits(5))
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
val decodeLoadStoreRegisterImmediatePreIndexed : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterImmediatePreIndexed ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b0@(imm9 : bits(9))@0b11@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = true;
  postindex : boolean = false;
  scale : range(0,3) = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate (opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,false);
}

function sharedDecodeLoadRegister(Rn:bits(5), Rt:bits(5), Rm:bits(5), opc : bits(2),size : bits(2),wback:boolean, postindex:boolean ,scale : range(0,3),extend_type : ExtendType, shift : range(0,3)) -> option(ast) = {
  n : reg_index = UInt_reg(Rn);
  t : reg_index = UInt_reg(Rt);
  m : reg_index = UInt_reg(Rm);
  acctype : AccType = AccType_NORMAL;
  memop : MemOp = MemOp_LOAD; /* ARM: uninitialized */
  _signed : boolean = b0; /* ARM: uninitialized */
  regsize : { 'R, RegisterSize('R). int('R) }/* int('R) */ = 64; /* ARM: uninitialized */

  if opc[1] == b0 then {
    /* store or zero-extending load */
    memop = if opc[0] == b1 then MemOp_LOAD else MemOp_STORE;
    regsize = if size == 0b11 then 64 else 32;
    _signed = false;
  } else {
    if size == 0b11 then {
      memop = MemOp_PREFETCH;
      if opc[0] == b1 then UnallocatedEncoding();
    } else {
      /* sign-extending load */
      memop = MemOp_LOAD;
      if size == 0b10 & opc[0] == b1 then UnallocatedEncoding();
      regsize = if opc[0] == b1 then 32 else 64;
      _signed = true;
    };
  };

  let datasize /* : {'D, DataSize('D). int('D)} */ /* : int('D) */ = lsl(8, scale);
  assert (datasize == 8 | datasize == 16 | datasize == 32 | datasize == 64); /* FIXME: CP: adding assertion so it typechecks */
  Some (LoadRegister (n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize));
}

/* LDR/STR (register) */
/* LDRB/STRB (register) */
/* LDRH/STRH (register) */
/* LDRSB (register) */
/* LDRSH (register) */
/* LDRSW (register) */
/* PRFM (register) */

val decodeLoadStoreRegisterRegisterOffset : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterRegisterOffset ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b1@(Rm:bits(5))@(option_v:bits(3))@[S]@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : range(0,3) = UInt(size);
  if option_v[1] == b0 then UnallocatedEncoding(); /* sub-word index */
  extend_type : ExtendType = DecodeRegExtend(option_v);
  shift : range(0,3) = if S == b1 then scale else 0;

  sharedDecodeLoadRegister(Rn,Rt,Rm,opc,size,wback,postindex,scale,extend_type,shift);
}

function clause execute ( LoadRegister((n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize as int('R),datasize as int('D))) ) = {
  offset : bits(64) = ExtendReg(m, extend_type, shift);
  address : bits(64) = Zeros(); /* ARM: uninitialized */
  data : bits('D) = Zeros(); /* ARM: uninitialized */
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
    /* announce the address */
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
        data = UNKNOWN_BITS() : bits('D)
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
      if _signed then {
        assert('R > 'D); /* FIXME: CP: adding assertion so it typechecks */
        wX(t) = SignExtend(data) : bits('R)
      }
      else {
        assert('R >= 'D); /* FIXME: CP: adding assertion so it typechecks */
        wX(t) = ZeroExtend(data) : bits('R);
      }
    },

    MemOp_PREFETCH  =>
      Prefetch(address,to_bits(t) : bits(5))
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

val decodeLoadStoreRegisterUnprivileged : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterUnprivileged ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b0@(imm9 : bits(9))@0b10@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : range(0,3) = UInt(size);
  offset : bits(64) = SignExtend(imm9);

  sharedDecodeLoadImmediate (opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_UNPRIV,false);
}

/* LDUR/STRUR */
/* LDURB/STURB */
/* LDURH/STURH */
/* LDURSB */
/* LDURSH */
/* LDURSW */
/* PRFUM */
val decodeLoadStoreRegisterUnscaledImmediate : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterUnscaledImmediate ((size:bits(2))@0b111@0b0@0b00@(opc:bits(2))@0b0@(imm9 : bits(9))@0b00@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : range(0,3) = UInt(size);
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
val decodeLoadStoreRegisterUnsignedImmediate : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterUnsignedImmediate ((size:bits(2))@0b111@0b0@0b01@(opc:bits(2))@(imm12 : bits(12))@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;
  scale : range(0,3) = UInt(size);
  offset : bits(64) = LSL(ZeroExtend(imm12), scale);

  sharedDecodeLoadImmediate (opc,size,Rn,Rt,wback,postindex,scale,offset,AccType_NORMAL,true);
}

function sharedDecodeLoadStorePair (L:boolean,opc : bits(2),imm7:bits(7),Rn:bits(5),Rt:bits(5),Rt2:bits(5),wback:boolean,postindex:boolean) -> option(ast) = {
  n : (reg_index) = UInt_reg(Rn);
  t : (reg_index) = UInt_reg(Rt);
  t2 : (reg_index) = UInt_reg(Rt2);
  acctype : (AccType) = AccType_NORMAL;
  memop : (MemOp) = if L == b1 then MemOp_LOAD else MemOp_STORE;
  if [L,opc[0]] == 0b01 | opc == 0b11 then UnallocatedEncoding();
  _signed : (boolean) = (opc[0] != b0);
  scale : range(2,3) = 2 + UInt([opc[1]]);
  let datasize /* : { 'D, DataSize('D). int('D) } */ = lsl(8, scale);
  assert (datasize == 8 | datasize == 16 | datasize == 32 | datasize == 64); /* FIXME: CP: adding assertion so it typechecks */
  offset : (bits(64)) = LSL(SignExtend(imm7), scale);

  Some(LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize,offset));
}

/* LDP signed offset */
/* LDPSW signed offset */
/* STP signed offset */
val decodeLoadStoreRegisterPairOffset : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterPairOffset (opc:bits(2)@0b101@0b0@0b010@[L]@(imm7 : bits(7))@(Rt2:bits(5))@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = false;
  postindex : boolean = false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

function clause execute ( LoadStorePair((wback,postindex,n,t,t2,acctype,memop,_signed,datasize as int('D),offset)) ) = {
  address : bits(64) = Zeros(); /* ARM: uninitialized */
  data1 : (bits('D)) = Zeros(); /* ARM: uninitialized */
  data2 : (bits('D)) = Zeros(); /* ARM: uninitialized */
  /*constant*/ let dbytes : {'db, 'db == div('D,8) & 'db in {1,2,4,8}. int('db) } = quot (datasize,8);
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
    /* announce the address */
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
        data1 = UNKNOWN_BITS() : (bits('D))
      else
        data1 = rX(t);
      if rt_unknown & t2 == n then
        data2 = UNKNOWN_BITS() : (bits('D))
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
        data1 = UNKNOWN_BITS() : bits('D);
        data2 = UNKNOWN_BITS() : bits('D);
      };
      if _signed then {
        assert('D < 64);  /*FIXME: CP adding assertion to make typecheck*/
        wX(t)  = (SignExtend(data1)) : (bits(64));
        wX(t2) = (SignExtend(data2)) : (bits(64));
      } else {
        wX(t)  = data1;
        wX(t2) = data2;
      };
    },
    _ => exit()
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
val decodeLoadStoreRegisterPairPostIndexed : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterPairPostIndexed ((opc:bits(2))@0b101@0b0@0b001@[L]@(imm7 : bits(7))@(Rt2:bits(5))@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = true;
  postindex : boolean = true;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

/* LDP pre-index */
/* LDPSW pre-index */
/* STP pre-index */
val decodeLoadStoreRegisterPairPreIndexed : bits(32) -> option(ast) effect {escape}
function decodeLoadStoreRegisterPairPreIndexed ((opc:bits(2))@0b101@0b0@0b011@[L]@(imm7 : bits(7))@(Rt2:bits(5))@(Rn:bits(5))@(Rt:bits(5))) = {
  wback : boolean = true;
  postindex : boolean = false;

  sharedDecodeLoadStorePair(L,opc,imm7,Rn,Rt,Rt2,wback,postindex);
}

/* ADD/ADDS (immediate) */
/* SUB/SUBS (immediate) */
val decodeAddSubtractImmediate : bits(32) -> option(ast) effect {escape}
function decodeAddSubtractImmediate ([sf]@[op]@[S]@0b10001@(shift:bits(2))@(imm12 : bits(12))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  let datasize : {| 32,64 |} = if sf == b1 then 64 else 32;
  sub_op : (boolean) = (op == b1);
  setflags : (boolean) = (S == b1);
  imm /* : (bits('R)) */ = Zeros(datasize); /* ARM: uninitialized */

  match shift {
    0b00  => imm = ZeroExtend(imm12),
    0b01  => imm = ZeroExtend(imm12 @ (0b0 ^^ 12)),
    [b1,_]  => ReservedValue()
  };

  Some(AddSubImmediate((d,n,datasize,sub_op,setflags,imm)));
}

function clause execute (AddSubImmediate((d,n,datasize as int('R),sub_op,setflags,imm))) = {
  operand1 : (bits('R)) = if n == 31 then rSP() else rX(n);
  operand2 : (bits('R)) = imm;
  carry_in : (bit) = b0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = b1;
  }
  else
    carry_in = b0;

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
val decodeBitfield : bits(32) -> option(ast) effect {escape}
function decodeBitfield ([sf]@(opc:bits(2))@0b100110@[N]@(immr : bits(6))@(imms : bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  let datasize : {|32,64|} = if sf == b1 then 64 else 32;
  /* let datasize as int('R) = datasize; */

  inzero : (boolean) = false; /* ARM: uninitialized */
  extend : (boolean) = false; /* ARM: uninitialized */
  R : range(0,63) = 0; /* ARM: uninitialized */
  S : range(0,63) = 0; /* ARM: uninitialized */

  match opc {
    0b00  => {inzero = true; extend = true},   /* SBFM */
    0b01  => {inzero = false; extend = false}, /* BFM */
    0b10  => {inzero = true; extend = false},  /* UBFM */
    0b11  => UnallocatedEncoding()
  };

  if sf == b1 & N != b1 then ReservedValue();
  if sf == b0 & (N != b0 | immr[5] != b0 | imms[5] != b0) then ReservedValue();

  let R = UInt(immr);
  let S = UInt(imms);

  let (wmask /* : bits('R) */, tmask /* : bits('R) */) = (DecodeBitMasks(datasize, N, imms, immr, false)) in {

  assert(R < datasize & S < datasize); /*FIXME: CP adding assertion to make typecheck*/

  Some(BitfieldMove((d,n,datasize,inzero,extend,R,S,wmask,tmask)));
}}


function clause execute (BitfieldMove((d,n,(datasize as int('R)),inzero,extend,R,S,wmask,tmask))) = {

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
val decodeExtract : bits(32) -> option(ast) effect {escape}
function decodeExtract ([sf]@0b00@0b100111@[N]@0b0@(Rm:bits(5))@(imms : bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  let datasize : {| 32,64 |} = if sf == b1 then 64 else 32;
  lsb : range(0,63) = 0; /* ARM: uninitialized */

  if N != sf then UnallocatedEncoding();
  if sf == b0 & imms[5] == b1 then ReservedValue();
  let lsb = UInt(imms);

  assert(lsb < datasize); /*FIXME: CP adding assertion to make typecheck*/
  Some(ExtractRegister((d,n,m,datasize,lsb)));
}

function clause execute ( ExtractRegister((d,n,m,datasize as int('R),lsb)) ) = {
  result : (bits('R)) = Zeros(); /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  concat : (bits(2*'R)) = operand1@operand2;
  result = concat[(lsb + datasize - 1)..lsb];
  wX(d) = result;
}

/* AND/ANDS (immediate) */
/* EOR (immediate) */
/* ORR (immediate) */
val decodeLogicalImmediate : bits(32) -> option(ast) effect {escape}
function decodeLogicalImmediate ([sf]@(opc:bits(2))@0b100100@[N]@(immr : bits(6))@(imms : bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  let datasize : {|32,64|} /* int('R) */ = if sf == b1 then 64 else 32;
  setflags : (boolean) = false; /* ARM: uninitialized */
  op : (LogicalOp) = LogicalOp_AND; /* ARM: uninitialized */
  match opc {
    0b00  => {op = LogicalOp_AND; setflags = false},
    0b01  => {op = LogicalOp_ORR; setflags = false},
    0b10  => {op = LogicalOp_EOR; setflags = false},
    0b11  => {op = LogicalOp_AND; setflags = true}
  };

  if sf == b0 & N != b0 then ReservedValue();
  let (imm,_) = (DecodeBitMasks(datasize,N, imms, immr, true)) in {

  Some(LogicalImmediate((d,n,datasize,setflags,op,imm)));
}}

function clause execute (LogicalImmediate((d,n,datasize as int('R),setflags,op,imm))) = {
  result : (bits('R)) = Zeros(); /* ARM: uninitialized */
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
val decodeMoveWideImmediate : bits(32) -> option(ast) effect {escape}
function decodeMoveWideImmediate ([sf]@(opc:bits(2))@0b100101@(hw : bits(2))@(imm16 : bits(16))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  let datasize : {|32,64|} /* : int('R) */ = if sf == b1 then 64 else 32;
  imm : (bits(16)) = imm16;
  pos : (uinteger) = 0; /* ARM: uninitialized */
  opcode : (MoveWideOp) = MoveWideOp_N; /* ARM: uninitialized */

  match opc {
    0b00  => opcode = MoveWideOp_N,
    0b10  => opcode = MoveWideOp_Z,
    0b11  => opcode = MoveWideOp_K,
    _  => UnallocatedEncoding()
  };

  if sf == b0 & hw[1] == b1 then UnallocatedEncoding();
  let pos = UInt(hw@0b0000);
  assert(pos < (datasize / 2));

  Some(MoveWide(d,datasize,imm,pos,opcode));
}

function clause execute ( MoveWide((d,datasize as int('R),imm,pos,opcode)) ) = {
  result : (bits('R)) = Zeros(); /* ARM: uninitialized */

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
val decodePCRelAddressing : bits(32) -> option(ast) effect {escape}
function decodePCRelAddressing ([op]@(immlo : bits(2))@0b10000@(immhi : bits(19))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  page : (boolean) = (op == b1);
  imm :(bits(64)) = Zeros(); /* ARM: uninitialized */

  if page then
    imm = SignExtend(immhi@immlo@(0b0 ^^ 12))
  else
    imm = SignExtend(immhi@immlo);

  Some(Address(d,page,imm))
}

function clause execute (Address(d,page,imm)) = {
  base : (bits(64)) = rPC();

  if page then
    base[11..0] = Zeros() : bits(12);

  wX(d) = base + imm;
}

/* ADD/ADDS (extended register) */
/* SUB/SUBS (extended register) */
val decodeAddSubtractExtendedRegister : bits(32) -> option(ast) effect {escape}
function decodeAddSubtractExtendedRegister ([sf]@[op]@[S]@0b01011@0b00@0b1@(Rm:bits(5))@(option_v:bits(3))@(imm3 : bits(3))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {|32,64|} /* : int('R) */ = if sf == b1 then 64 else 32;
  sub_op : (boolean) = (op == b1);
  setflags : (boolean) = (S == b1);
  extend_type : (ExtendType) = DecodeRegExtend(option_v);
  shift : range(0,7) = UInt(imm3);
  if shift > 4 then ReservedValue();

  Some(AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift));
}

function clause execute (AddSubExtendRegister((d,n,m,datasize as int('R),sub_op,setflags,extend_type,shift))) = {
  operand1 : (bits('R)) = if n == 31 then rSP() else rX(n);
  operand2 : (bits('R)) = ExtendReg(m, extend_type, shift);
  carry_in : (bit) = b0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = b1;
  } else
    carry_in = b0;

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
val decodeAddSubtractShiftedRegister : bits(32) -> option(ast) effect {escape}
function decodeAddSubtractShiftedRegister ([sf]@[op]@[S]@0b01011@(shift:bits(2))@0b0@(Rm:bits(5))@(imm6 : bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {| 32,64 |} /* : int('R) */ = if sf == b1 then 64 else 32;
  sub_op : (boolean) = (op == b1);
  setflags : (boolean) = (S == b1);

  if shift == 0b11 then ReservedValue();
  if sf == b0 & imm6[5] == b1 then ReservedValue();

  shift_type : (ShiftType) = DecodeShift(shift);
  shift_amount : range(0,63) = UInt(imm6);

  Some(AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount));
}

function clause execute (AddSubShiftedRegister((d,n,m,(datasize as int('R)),sub_op,setflags,shift_type,shift_amount))) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = ShiftReg(m, shift_type, shift_amount);
  carry_in : (bit) = b0; /* ARM: uninitialized */

  if sub_op then {
    operand2 = NOT(operand2);
    carry_in = b1;
  }
  else
    carry_in = b0;

  let (result,nzcv) = AddWithCarry(operand1, operand2, carry_in) in {

    if setflags then
      wPSTATE_NZCV() = nzcv;

    wX(d) = result;
  }
}

/* ADC/ADCS */
/* SBC/SBCS */


val decodeAddSubtractWithCarry : bits(32) -> option(ast) effect {escape}
function decodeAddSubtractWithCarry ([sf]@[op]@[S]@0b11010000@(Rm:bits(5))@0b000000@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {| 32, 64 |} /* (int('R)) */ = if sf == b1 then 64 else 32;
  sub_op : (boolean) = (op == b1);
  setflags : (boolean) = (S == b1);

  Some(AddSubCarry(d,n,m,datasize,sub_op,setflags));
}

function clause execute( AddSubCarry((d,n,m,(datasize as int('R)),sub_op,setflags))) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  if sub_op then
    operand2 = NOT(operand2);

  let (result,nzcv) = AddWithCarry (operand1, operand2, PSTATE_C()[0]) in {

  if setflags then
    wPSTATE_NZCV() = nzcv;

  wX(d) = result;
}}

/* CCMN (immediate) */
/* CCMP (immediate) */
val decodeConditionalCompareImmediate : bits(32) -> option(ast) effect pure
function decodeConditionalCompareImmediate ([sf]@[op]@0b1@0b11010010@(imm5 : bits(5))@(_cond:bits(4))@0b1@0b0@(Rn:bits(5))@0b0@(nzcv:bits(4))) = {
  n : (reg_index) = UInt_reg(Rn);
  let datasize : {| 32, 64 |} /* : int('R) */ = if sf == b1 then 64 else 32;
  sub_op : boolean = (op == b1);
  condition : bits(4) = _cond;
  flags : bits(4) = nzcv;
  imm /* : bits('R) */ = ZeroExtend(datasize,imm5);

  Some(ConditionalCompareImmediate((n,datasize,sub_op,condition,flags,imm)));
}

function clause execute(ConditionalCompareImmediate((n,datasize as int('R),sub_op,condition,flags,imm))) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = imm;
  carry_in : (bit) = b0;

  flags' : (bits(4)) = flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = NOT(operand2);
      carry_in = b1;
    };
    let (_,nzcv) =  AddWithCarry(operand1, operand2, carry_in) in {flags' = nzcv};
  };
  wPSTATE_NZCV() = flags';
}

/* CCMN (register) */
/* CCMP (register) */
val decodeConditionalCompareRegister : bits(32) -> option(ast) effect pure
function decodeConditionalCompareRegister ([sf]@[op]@0b1@0b11010010@(Rm:bits(5))@ (_cond:bits(4))@0b0@0b0@(Rn:bits(5))@0b0@(nzcv:bits(4))) = {
  n : reg_index = UInt_reg(Rn);
  m : reg_index = UInt_reg(Rm);
  datasize : {|32,64|} /* : int('R) */ = if sf == b1 then 64 else 32;
  sub_op : boolean = (op == b1);
  condition : bits(4) = _cond;
  flags : bits(4) = nzcv;

  Some(ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags));
}

function clause execute (ConditionalCompareRegister((n,m,datasize as int('R),sub_op,condition,flags))) = {
  operand1 : bits('R) = rX(n);
  operand2 : bits('R) = rX(m);
  carry_in : bit = b0;

  flags' : bits(4) = flags;
  if ConditionHolds(condition) then {
    if sub_op then {
      operand2 = NOT(operand2);
      carry_in = b1;
    };
    let (_,nzcv) = AddWithCarry (operand1, operand2, carry_in) in {flags' = nzcv};
  };
  wPSTATE_NZCV() = flags';
}

/* CSEL op=0,o2=0 */
/* CSINC op=0,o2=1 */
/* CSINV op=1,o2=0 */
/* CSNEG op=1,o2=1 */
val decodeConditionalSelect : bits(32) -> option(ast) effect pure
function decodeConditionalSelect ([sf]@[op]@0b0@0b11010100@(Rm:bits(5))@(_cond:bits(4))@0b0@[o2]@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {|32,64|}/* (int('R)) */ = if sf == b1 then 64 else 32;
  condition : (bits(4)) = _cond;
  else_inv : (boolean) = (op == b1);
  else_inc : (boolean) = (o2 == b1);

  Some(ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc));
}

function clause execute ( ConditionalSelect((d,n,m,datasize as int('R),condition,else_inv,else_inc)) ) = {
  result : (bits('R)) = Zeros(); /* ARM: uninitialized */
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

val decodeData1Source : bits(32) -> option(ast) effect {escape}
scattered function decodeData1Source

/* RBIT */
/* REV */
/* REV16 */
/* REV32 */
function clause decodeData1Source ([sf]@0b1@0b0@0b11010110@0b00000@0b0000@(opc:bits(2))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);

  datasize : {|32,64|}/* (int('R)) */ = if sf == b1 then 64 else 32;

  op : (RevOp) = RevOp_RBIT; /* ARM: uninitialized */
  match opc {
    0b00  =>
      op = RevOp_RBIT,
    0b01  =>
      op = RevOp_REV16,
    0b10  =>
      op = RevOp_REV32,
    0b11  => {
      if sf == b0 then UnallocatedEncoding();
      op = RevOp_REV64;
    }
  };

  Some(Reverse(d,n,datasize,op));
}

function clause execute ( Reverse((d,n,datasize as int('R),op)) ) = {
  result : (bits('R)) = Zeros(); /* ARM uninitialized */
  /* let V : (bits(6)) = Zeros(); /\* ARM uninitialized *\/ */

  let V : (bits(6)) = match op {
    RevOp_REV16  => /* V = */ 0b001000,
    RevOp_REV32  => /* V = */ 0b011000,
    RevOp_REV64  => /* V = */ 0b111000,
    RevOp_RBIT  =>  /* V = */ if datasize == 64 then 0b111111 else 0b011111
  };

  result : (bits('R)) = rX(n);

  foreach (vbit from 0 to 5) {
    /* Swap pairs of 2^vbit bits in result */
    if V[vbit] == b1 then {
      tmp : (bits('R)) = result;
      let vsize /* : (uinteger) */ = lsl(1, vbit);
      assert (vsize > 0); /* FIXME: CP adding assertion to make typecheck */
      foreach (base from 0 to (datasize - 1) by (2 * vsize)) { /* ARM: while base < datasize do */
        assert (base+vsize*2 - 1 < datasize); /* FIXME: CP adding assertion to make typecheck */
/*        let a = tmp[(base+(2*vsize) - 1)..(base+vsize)];
        result[((base+vsize) - 1)..base] = a;
        let b = tmp[(base+vsize - 1)..base];
        result[(base+(2*vsize) - 1)..(base+vsize)] = b;*/
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
function clause decodeData1Source ([sf]@0b1@0b0@0b11010110@0b00000@0b00010@[op]@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  datasize : {| 32,64 |} /* (int('R)) */ = if sf == b1 then 64 else 32;
  opcode : (CountOp) = if op == b0 then CountOp_CLZ else CountOp_CLS;

  Some(CountLeading(d,n,datasize,opcode));
}

function clause execute (CountLeading((d,n,datasize as int('R),opcode))) = {
  result : integer = 0; /* ARM: uninitialized */
  operand1 : (bits('R)) = rX(n);

  if opcode == CountOp_CLZ then
    result = CountLeadingZeroBits(operand1)
  else
    result = CountLeadingSignBits(operand1);

  wX(d) = to_bits(result) : bits('R);
}

end decodeData1Source

val decodeData2Source : bits(32) -> option(ast) effect {escape}
scattered function decodeData2Source

/* SDIV o1=1 */
/* UDIV o1=0 */
function clause decodeData2Source ([sf]@0b0@0b0@0b11010110@(Rm:bits(5))@0b00001@[o1]@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {| 32, 64 |} /* (int('R)) */ = if sf == b1 then 64 else 32;
  _unsigned : (boolean) = (o1 == b0);

  Some(Division(d,n,m,datasize,_unsigned));
}

function clause execute ( Division((d,n,m,datasize as int('R),_unsigned)) ) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);
  result : (integer) = 0; /* ARM: uninitialized */

  if IsZero(operand2) then
    result = 0
  else
    result = /* ARM: RoundTowardsZero*/ tdiv_int (_Int(operand1, _unsigned), _Int(operand2, _unsigned));

  wX(d) = to_bits(result) : (bits('R)) ; /* ARM: result[(datasize-1)..0] */
}

/* ASRV */
/* LSLV */
/* LSRV */
/* RORV */
function clause decodeData2Source ([sf]@0b0@0b0@0b11010110@(Rm:bits(5))@0b0010@(op2:bits(2))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {| 32, 64 |} /* (int('R)) */ = if sf == b1 then 64 else 32;
  shift_type : (ShiftType) = DecodeShift(op2);

  Some(Shift(d,n,m,datasize,shift_type));
}

function clause execute (Shift((d,n,m,datasize as int('R),shift_type))) = {
  result : (bits('R)) = Zeros(); /* ARM: uninitialized */
  operand2 : (bits('R)) = rX(m);

  result = ShiftReg(n, shift_type, mod (UInt(operand2), datasize));
  wX(d) = result;
}

/* CRC32B/CRC32H/CRC32W/CRC32X C=0 */
/* CRC32CB/CRC32CH/CRC32CW/CRC32CX C=1 */
function clause decodeData2Source ([sf]@0b0@0b0@0b11010110@(Rm:bits(5))@0b010@[C]@(sz:bits(2))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  if sf == b1 & sz != 0b11 then UnallocatedEncoding();
  if sf == b0 & sz == 0b11 then UnallocatedEncoding();
  let size /* : {| 8,16,32,64 |} */ /* (int('D)) */ = lsl(8, UInt(sz)); /* 2-bit size field -> 8, 16, 32, 64 */
  assert (size == 8 | size == 16 | size == 32 | size == 64); /*FIXME: CP adding assertion to make typecheck*/
  crc32c : (boolean) = (C == b1);

  Some(CRC(d,n,m,size,crc32c));
}

function clause execute ( CRC((d,n,m,(size as int('D)),crc32c)) ) = {
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

val decodeData3Source : bits(32) -> option(ast) effect pure
scattered function decodeData3Source

/* MADD o0=0 */
/* MSUB o0=1 */
function clause decodeData3Source ([sf]@0b00@0b11011@0b000@(Rm:bits(5))@[o0]@(Ra:bits(5))@(Rn:bits(5))@(Rd:bits(5))) = {
  let d : (reg_index) = UInt_reg(Rd);
  let n : (reg_index) = UInt_reg(Rn);
  let m : (reg_index) = UInt_reg(Rm);
  let a : (reg_index) = UInt_reg(Ra);
  let destsize /* (int('R)) */ = if sf == b1 then 64 else 32;
  let datasize /* (int('D)) */ = destsize;
  let sub_op : (boolean) = (o0 == b1);

  Some(MultiplyAddSub((d,n,m,a,destsize,datasize,sub_op)));
}

function clause execute ( MultiplyAddSub((d,n,m,a,destsize as int('D),datasize as int('R),sub_op)) ) = {
  operand1 : (bits('D)) = rX(n);
  operand2 : (bits('D)) = rX(m);
  operand3 : (bits('R)) = rX(a);

  result : (integer) = 0; /* ARM: uninitialized */

  if sub_op then
    result = UInt(operand3) - (UInt(operand1) * UInt(operand2))
  else
    result = UInt(operand3) + (UInt(operand1) * UInt(operand2));

  wX(d) = to_bits(result) : (bits('R));
}

/* SMADDL */
/* SMSUBL */
/* UMADDL */
/* UMSUBL */
function clause decodeData3Source (0b1@0b00@0b11011@[U]@0b01@(Rm:bits(5))@[o0]@(Ra:bits(5))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  a : (reg_index) = UInt_reg(Ra);
  destsize /* : (int('R)) */ = 64;
  datasize /* : (int('D)) */ = 32;
  sub_op : (boolean) = (o0 == b1);
  _unsigned : (boolean) = (U == b1);

  Some(MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned));
}

function clause execute ( MultiplyAddSubLong((d,n,m,a,destsize as int('R),datasize as int('D),sub_op,_unsigned)) ) = {
  operand1 : (bits('D)) = rX(n);
  operand2 : (bits('D)) = rX(m);
  operand3 : (bits('R)) = rX(a);

  result : (integer) = 0; /* ARM: uninitialized */

  if sub_op then
    result = _Int(operand3, _unsigned) - (_Int(operand1, _unsigned) * _Int(operand2, _unsigned))
  else
    result = _Int(operand3, _unsigned) + (_Int(operand1, _unsigned) * _Int(operand2, _unsigned));

  wX(d) = to_bits(result) : (bits(64));
}

/* SMULH */
/* UMULH */
function clause decodeData3Source (0b1@0b00@0b11011@[U]@0b10@(Rm:bits(5))@0b0@(Ra:bits(5))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  a : (reg_index) = UInt_reg(Ra); /* ignored by UMULH/SMULH */
  destsize /* : (int('R)) */ = 64;
  datasize /* : (int('D)) */ = destsize;
  _unsigned : (boolean) = (U == b1);

  Some(MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned));
}

function clause execute ( MultiplyHigh((d,n,m,a,destsize as int('R),datasize,_unsigned)) ) = {
  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = rX(m);

  /* result : (integer) = 0; /\* ARM: uninitialized *\/ */

  result = _Int(operand1, _unsigned) * _Int(operand2, _unsigned);

  wX(d) = (to_bits(result) : bits(128))[127..64];
}

end decodeData3Source

/* AND/ANDS (shifted register) */
/* EON (shifted register) */
/* EOR (shifted register) */
/* ORN (shifted register) */
/* ORR (shifted register) */
/* BIC/BICS (shifted register) */
val decodeLogicalShiftedRegister : bits(32) -> option(ast) effect {escape}
function decodeLogicalShiftedRegister ([sf]@(opc:bits(2))@0b01010@(shift:bits(2))@[N]@(Rm:bits(5))@(imm6 : bits(6))@(Rn:bits(5))@(Rd:bits(5))) = {
  d : (reg_index) = UInt_reg(Rd);
  n : (reg_index) = UInt_reg(Rn);
  m : (reg_index) = UInt_reg(Rm);
  datasize : {| 32,64 |} /* : (int('R)) */ = if sf == b1 then 64 else 32;
  setflags : (boolean) = false; /* ARM: uninitialized */
  op : (LogicalOp) = LogicalOp_AND; /* ARM: uninitialized */
  match opc {
    0b00  => {op = LogicalOp_AND; setflags = false},
    0b01  => {op = LogicalOp_ORR; setflags = false},
    0b10  => {op = LogicalOp_EOR; setflags = false},
    0b11  => {op = LogicalOp_AND; setflags = true}
  };

  if sf == b0 & imm6[5] == b1 then ReservedValue();

  shift_type : (ShiftType) = DecodeShift(shift);
  shift_amount : range(0,63) = UInt(imm6);
  invert : (boolean) = (N == b1);

  Some(LogicalShiftedRegister((d,n,m,datasize,setflags,op,shift_type,shift_amount,invert)))
}

function clause execute (LogicalShiftedRegister((d,n,m,datasize as int('R),setflags,op,shift_type,shift_amount,invert))) = {

  operand1 : (bits('R)) = rX(n);
  operand2 : (bits('R)) = ShiftReg(m, shift_type, shift_amount);

  if invert then operand2 = NOT(operand2);

  result : (bits('R)) = Zeros(); /* ARM: uninitialized */
  match op {
    LogicalOp_AND  => result = (operand1 & operand2),
    LogicalOp_ORR  => result = (operand1 | operand2),
    LogicalOp_EOR  => result = (operand1 ^ operand2)
  };

  if setflags then
    wPSTATE_NZCV() = ([result[datasize - 1]]@[IsZeroBit(result)]@0b00);

  wX(d) = result;
}

val decodeDataSIMDFPoint1 : bits(32) -> option(ast) effect {escape}
function decodeDataSIMDFPoint1 (machineCode) = {
  not_implemented("decodeDataSIMDFPoint1");
  Some(Unallocated());
}

val decodeDataSIMDFPoint2 : bits(32) -> option(ast) effect {escape}
function decodeDataSIMDFPoint2 ( machineCode) = {
  not_implemented("decodeDataSIMDFPoint2");
  Some(Unallocated());
}

val decodeDataRegister : bits(32) -> option(ast) effect {escape}
function decodeDataRegister (machineCode) = {
  match machineCode {
    ([_]@[_]@[_]@0b0@ 0b1@0b0@0b1@0b0@ [_]@[_]@[_]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeLogicalShiftedRegister(machineCode),
    ([_]@[_]@[_]@0b0@ 0b1@0b0@0b1@0b1@ [_]@[_]@0b0@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractShiftedRegister(machineCode),
    ([_]@[_]@[_]@0b0@ 0b1@0b0@0b1@0b1@ [_]@[_]@0b1@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractExtendedRegister(machineCode),
    ([_]@[_]@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b0@0b0@0b0@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeAddSubtractWithCarry(machineCode),
    ([_]@[_]@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b0@0b1@0b0@ (_ : bits(9)) @0b0@(_ : bits(11)))  => decodeConditionalCompareRegister(machineCode),
    ([_]@[_]@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b0@0b1@0b0@ (_ : bits(9)) @0b1@(_ : bits(11)))  => decodeConditionalCompareImmediate(machineCode),
    ([_]@[_]@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b1@0b0@0b0@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeConditionalSelect(machineCode),
    ([_]@[_]@[_]@0b1@ 0b1@0b0@0b1@0b1@ [_]@[_]@[_]@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData3Source(machineCode),
    ([_]@0b0@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b1@0b1@0b0@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData2Source(machineCode),
    ([_]@0b1@[_]@0b1@ 0b1@0b0@0b1@0b0@ 0b1@0b1@0b0@ (_ : bits(9)) @[_]@(_ : bits(11)))  => decodeData1Source(machineCode)
  }
}

val decodeDataImmediate : bits(32) -> option(ast) effect {escape}
function decodeDataImmediate (machineCode) = {
  match machineCode {
    ((_ : bits(3))@0b1@0b0@0b0@0b0@0b0@[_]@(_ : bits(23)))  => decodePCRelAddressing(machineCode),
    ((_ : bits(3))@0b1@0b0@0b0@0b0@0b1@[_]@(_ : bits(23)))  => decodeAddSubtractImmediate(machineCode),
    ((_ : bits(3))@0b1@0b0@0b0@0b1@0b0@0b0@(_ : bits(23)))  => decodeLogicalImmediate(machineCode),
    ((_ : bits(3))@0b1@0b0@0b0@0b1@0b0@0b1@(_ : bits(23)))  => decodeMoveWideImmediate(machineCode),
    ((_ : bits(3))@0b1@0b0@0b0@0b1@0b1@0b0@(_ : bits(23)))  => decodeBitfield(machineCode),
    ((_ : bits(3))@0b1@0b0@0b0@0b1@0b1@0b1@(_ : bits(23)))  => decodeExtract(machineCode)
  }
}

val decodeLoadsStores : bits(32) -> option(ast) effect {escape}
function decodeLoadsStores (machineCode) = {
  match machineCode {
    ([_]@[_]@0b0@0b0@ 0b1@0b0@0b0@0b0@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreExclusive(machineCode),
    ([_]@[_]@0b0@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadRegisterLiteral(machineCode),
    ([_]@[_]@0b1@0b0@ 0b1@[_]@0b0@0b0@ 0b0@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreNoAllocatePairOffset(machineCode),
    ([_]@[_]@0b1@0b0@ 0b1@[_]@0b0@0b0@ 0b1@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairPostIndexed(machineCode),
    ([_]@[_]@0b1@0b0@ 0b1@[_]@0b0@0b1@ 0b0@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairOffset(machineCode),
    ([_]@[_]@0b1@0b0@ 0b1@[_]@0b0@0b1@ 0b1@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterPairPreIndexed(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@0b0@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @0b0@0b0@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnscaledImmediate(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@0b0@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @0b0@0b1@ (_ : bits(10)) )  => decodeLoadStoreRegisterImmediatePostIndexed(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@0b0@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @0b1@0b0@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnprivileged(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@0b0@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @0b1@0b1@ (_ : bits(10)) )  => decodeLoadStoreRegisterImmediatePreIndexed(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b0@ [_]@[_]@0b1@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @0b1@0b0@ (_ : bits(10)) )  => decodeLoadStoreRegisterRegisterOffset(machineCode),
    ([_]@[_]@0b1@0b1@ 0b1@[_]@0b0@0b1@ [_]@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeLoadStoreRegisterUnsignedImmediate(machineCode),
    (0b0@[_]@0b0@0b0@ 0b1@0b1@0b0@0b0@ 0b0@[_]@0b0@0b0@ 0b0@0b0@0b0@0b0@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreMultiStruct(machineCode),
    (0b0@[_]@0b0@0b0@ 0b1@0b1@0b0@0b0@ 0b1@[_]@0b0@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreMultiStructPostIndexed(machineCode),
    (0b0@[_]@0b0@0b0@ 0b1@0b1@0b0@0b1@ 0b0@[_]@[_]@0b0@ 0b0@0b0@0b0@0b0@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreSingleStruct(machineCode),
    (0b0@[_]@0b0@0b0@ 0b1@0b1@0b0@0b1@ 0b1@[_]@[_]@[_]@ [_]@[_]@[_]@[_]@ (_ : bits(4)) @[_]@[_]@ (_ : bits(10)) )  => decodeAdvSIMDLoadStoreSingleStructPostIndexed(machineCode)
  }
}

val decodeSystemImplementationDefined : bits(32) -> option(ast) effect {escape}
function decodeSystemImplementationDefined (machineCode) = {
  match machineCode {
    ((_ : bits(11)) @0b0@0b1@[_]@[_]@[_]@0b1@[_]@0b1@0b1@(_ : bits(12)))  => decodeImplementationDefined(machineCode),
    ((_ : bits(11)) @0b1@0b1@[_]@[_]@[_]@0b1@[_]@0b1@0b1@(_ : bits(12)))  => decodeImplementationDefined(machineCode),
    ((_ : bits(11)) @[_]@[_]@[_]@[_]@[_]@[_]@[_]@[_]@[_]@(_ : bits(12)))  => decodeSystem(machineCode)
  }
}


val decodeBranchesExceptionSystem : bits(32) -> option(ast) effect {escape}
function decodeBranchesExceptionSystem (machineCode) = {
  match machineCode {
    ([_]@0b0@0b0@0b1@0b0@0b1@[_]@[_]@[_]@[_]@(_ : bits(22)))  => decodeUnconditionalBranchImmediate(machineCode),
    ([_]@0b0@0b1@0b1@0b0@0b1@0b0@[_]@[_]@[_]@(_ : bits(22)))  => decodeCompareBranchImmediate(machineCode),
    ([_]@0b0@0b1@0b1@0b0@0b1@0b1@[_]@[_]@[_]@(_ : bits(22)))  => decodeTestBranchImmediate(machineCode),
    (0b0@0b1@0b0@0b1@0b0@0b1@0b0@[_]@[_]@[_]@(_ : bits(22)))  => decodeConditionalBranchImmediate(machineCode),
    (0b1@0b1@0b0@0b1@0b0@0b1@0b0@0b0@[_]@[_]@(_ : bits(22)))  => decodeExceptionGeneration(machineCode),
    (0b1@0b1@0b0@0b1@0b0@0b1@0b0@0b1@0b0@0b0@(_ : bits(22)))  => decodeSystemImplementationDefined(machineCode),
    (0b1@0b1@0b0@0b1@0b0@0b1@0b1@[_]@[_]@[_]@(_ : bits(22)))  => decodeUnconditionalBranchRegister(machineCode)
  }
}

val decode : bits(32) -> option(ast) effect {escape}
function decode (machineCode) = {
  match machineCode {
    ((_ : bits(3)) @0b0@0b0@[_]@[_]@(_ : bits(25)))  => Some(Unallocated()),
    ((_ : bits(3)) @0b1@0b0@0b0@[_]@(_ : bits(25)))  => decodeDataImmediate(machineCode),
    ((_ : bits(3)) @0b1@0b0@0b1@[_]@(_ : bits(25)))  => decodeBranchesExceptionSystem(machineCode),
    ((_ : bits(3)) @[_]@0b1@[_]@0b0@(_ : bits(25)))  => decodeLoadsStores(machineCode),
    ((_ : bits(3)) @[_]@0b1@0b0@0b1@(_ : bits(25)))  => decodeDataRegister(machineCode),
    ((_ : bits(3)) @0b0@0b1@0b1@0b1@(_ : bits(25)))  => decodeDataSIMDFPoint1(machineCode),
    ((_ : bits(3)) @0b1@0b1@0b1@0b1@(_ : bits(25)))  => decodeDataSIMDFPoint2(machineCode),
    _                                                => None()
  }
}
    
end execute

val supported_instructions : ast -> option(ast) effect {escape}
function supported_instructions (instr) = {
  match instr {
    Unallocated () => None (),
    _  => Some(instr)
  }
}
