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

val rmem_kind : (AccType, bool) -> instruction_kind 
function rmem_kind (acctype, exclusive) =
  if exclusive then
    match acctype {
      AccType_ATOMIC   => IK_mem_read(Read_exclusive),
      AccType_ORDERED  => IK_mem_read(Read_exclusive_acquire),
      _  => { not_implemented("unimplemented memory access");
                  IK_mem_read(Read_exclusive); }
    }
  else
    match acctype {
      AccType_NORMAL   => IK_mem_read(Read_plain),
      AccType_ATOMIC   => IK_mem_read(Read_plain),
      AccType_STREAM   => IK_mem_read(Read_stream),
      AccType_UNPRIV   => IK_mem_read(Read_plain),
      AccType_ORDERED  => IK_mem_read(Read_acquire)
    }


function instruction_kind wmem_kind (acctype : (AccType), exclusive : (bool)) =
  if exclusive then {
    match acctype {
      AccType_ATOMIC   => IK_mem_write(Write_exclusive),
      AccType_ORDERED  => IK_mem_write(Write_exclusive_release),
      _  => { not_implemented("unimplemented memory access");
                  IK_mem_write(Write_exclusive); }
    }
  } else {
    match acctype {
      AccType_NORMAL   => IK_mem_write(Write_plain),
      AccType_STREAM   => IK_mem_write(Write_plain),
      AccType_UNPRIV   => IK_mem_write(Write_plain),
      AccType_ORDERED  => IK_mem_write(Write_release),
      _  => { not_implemented("unimplemented memory access");
                  IK_mem_write(Write_plain) }
    };
  }


let _Rs : vector(31,dec,string) =
  ["R30","R29","R28","R27","R26","R25","R24","R23","R22","R21",
   "R20","R19","R18","R17","R16","R15","R14","R13","R12","R11",
   "R10","R9" ,"R8" ,"R7" ,"R6" ,"R5" ,"R4" ,"R3" ,"R2" ,"R1" ,
   "R0"]

let TxNestingLevelfp  = RFull("TxNestingLevel")
let TXIDR_EL0_DEPTHfp = RField("TXIDR_EL0","DEPTH")

let PSTATE_Nfp  = RField("NZCV","N")
let PSTATE_Zfp  = RField("NZCV","Z")
let PSTATE_Cfp  = RField("NZCV","C")
let PSTATE_Vfp  = RField("NZCV","V")
let PSTATE_Dfp  = RField("DAIF","D")
let PSTATE_Afp  = RField("DAIF","A")
let PSTATE_Ifp  = RField("DAIF","I")
let PSTATE_Ffp  = RField("DAIF","F")
let PSTATE_ELfp = RFull("CurrentEL")
let PSTATE_SPfp = RField("SPSel","SP")
let _PCfp       = RFull("_PC")

let NZCVfp = [| PSTATE_Nfp, PSTATE_Zfp, PSTATE_Cfp, PSTATE_Vfp |]

function regfps xFP(n : (reg_index)) =
  if n != 31 then [|RFull(_Rs[n])|] else [| |]


/* check if this is still what we want */
function BranchToFP forall 'N, 'N in {32,64}.  (iR,oR) -> (regfps,regfps) =
  (if UsingAArch32() then iR else PSTATE_ELfp :: iR, _PCfp :: oR)

function regfps ConditionHoldsIFP(_cond : (bits(4))) =
  match _cond[3..1] {
    0b000  => [| PSTATE_Zfp |],
    0b001  => [| PSTATE_Cfp |],
    0b010  => [| PSTATE_Nfp |],
    0b011  => [| PSTATE_Vfp |],
    0b100  => [| PSTATE_Cfp, PSTATE_Zfp |],
    0b101  => [| PSTATE_Nfp, PSTATE_Vfp |],
    0b110  => [| PSTATE_Nfp, PSTATE_Vfp, PSTATE_Zfp |],
    0b111  => [| |]
  }

/* for iR if rSPFP, for oR if wSPFP */
let rSPIFP = 
  /* TODO: actually this depends on runtime data: PSTATE_SP and PSTATE_EL */
  [| PSTATE_SPfp, RFull("SP_EL0") |]

let wSPFP = 
  /* TODO: actually this depends on runtime data: PSTATE_SP and PSTATE_EL */
  ([| PSTATE_SPfp |],
   [| RFull("SP_EL0") |])


let CheckSPAlignmentIFP = PSTATE_ELfp :: rSPIFP

let BigEndianIFP =
  if UsingAArch32() then [| RFull("PSTATE_E") |] else [| PSTATE_ELfp |] 

let wMem'IFP = BigEndianIFP 
let wMemIFP = wMem'IFP

function initial_analysis (instr) -> (regfps,regfps,regfps,niafps,diafp,instruction_kind) = {
  iR = [| |];
  oR = [| |];
  aR = [| |];
  Nias = [| NIAFP_successor |];
  Dia = DIAFP_none;
  ik = IK_simple;

  match instr {
    (TMStart(t))  => {
      iR = TxNestingLevelfp :: TXIDR_EL0_DEPTHfp :: iR;
      /* TODO: whether the following applies depends on runtime data:
         ~(TxNestingLevel >= TXIDR_EL0.DEPTH) */
      oR = TxNestingLevelfp :: append(oR,xFP(t));
      ik = IK_trans(Transaction_start);
    },
    (TMCommit)  => {
      iR = TxNestingLevelfp :: iR;
      oR = TxNestingLevelfp :: oR;
      ik = IK_trans(Transaction_commit);
    },
    (TMAbort(retry,reason))  => {
      iR = TxNestingLevelfp :: iR;
      ik = IK_trans(Transaction_abort);
    },
    (TMTest)  => {
      iR = TxNestingLevelfp :: iR;
      oR = RFull("NZCV") :: oR;
    },
    (CompareAndBranch(t,datasize,iszero,offset))  => {
      iR = append(iR,xFP(t));
      /* TODO: whether the following applies depends on runtime data:
         IsZero(operand1) */
      let (i,o) = BranchToFP(iR,oR) in {iR = i; oR = o};
      nia' : (bits(64)) = rPC() + offset;
      Nias = [| NIAFP_successor, NIAFP_concrete_address(nia') |];
      ik = IK_branch;
    },
    (BranchConditional(offset,condition))  => {
      iR = append(iR,ConditionHoldsIFP(condition));
      /* TODO: whether the following applies depends on runtime data:
         ConditionHolds(condition) */
      let (i,o) = BranchToFP(iR,oR) in {iR = i; oR = o};
      Nias = [| NIAFP_successor, NIAFP_concrete_address(rPC() + offset) |];
      ik = IK_branch;
    },
    (GenerateExceptionEL1(imm))  => not_implemented("GenerateExceptionEL1"),
    (GenerateExceptionEL2(imm))  => not_implemented("GenerateExceptionEL2"),
    (GenerateExceptionEL3(imm))  => not_implemented("GenerateExceptionEL3"),
    (DebugBreakpoint(comment))  => not_implemented("DebugBreakpoint"),
    (ExternalDebugBreakpoint)  => not_implemented("ExternalDebugBreakpoint"),
    (DebugSwitchToExceptionLevel(target_level))  => not_implemented("DebugSwitchToExceptionLevel"),
    (MoveSystemImmediate(operand,field))  =>
      match field {
        PSTATEField_SP  => oR = PSTATE_SPfp :: oR,
        PSTATEField_DAIFSet  => {
          iR = append(iR, [| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp |]);
          oR = append(oR, [| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp |]);
        },
        PSTATEField_DAIFClr  => {
          iR = append(iR, [| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp |]);
          oR = append(oR, [| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp |]);
        }
      },
    (Hint(op))  => 
      match op {
        SystemHintOp_YIELD  => (),
        SystemHintOp_WFE  => {
          if EventRegistered() then () /* ClearEventRegister */
          else {
            /* the execute code for this case always fails because of
               WaitForEvent, declared as extern but not defined */
            not_implemented("Hint(SystemHintOp_WFE);") 
          }
        },
        SystemHintOp_WFI  => {
            /* the execute code for this case always fails because of
               InterruptPending, declared as extern but not defined */
            not_implemented("Hint(SystemHintOp_WFI);") 
        },
        SystemHintOp_SEV  => (), /*SendEvent*/
        SystemHintOp_SEVL  =>
            /* the execute code for this case always fails because of
               EventRegisterSet, declared as extern but not defined */
            not_implemented("Hint(SystemHintOp_SEVL);"),
        _  => () /* do nothing */ 
      },
    (ClearExclusiveMonitor(imm))  => (), /*ClearExclusiveLocal*/
    (Barrier(op,domain,types))  => {
      ik = match op {
        MemBarrierOp_DSB  =>
          match types {
            MBReqTypes_Reads   => IK_barrier(Barrier_DSB_LD),
            MBReqTypes_Writes  => IK_barrier(Barrier_DSB_ST),
            MBReqTypes_All     => IK_barrier(Barrier_DSB)
          },
        MemBarrierOp_DMB  => 
          match types {
            MBReqTypes_Reads   => IK_barrier(Barrier_DMB_LD),
            MBReqTypes_Writes  => IK_barrier(Barrier_DMB_ST),
            MBReqTypes_All     => IK_barrier(Barrier_DMB)
          },
        MemBarrierOp_ISB  =>
          IK_barrier(Barrier_ISB)
      };
    },
    (System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result))  => {
      oR = append(oR,xFP(t));
      not_implemented("System"); /* because SysOp_R and SysOp_W */
    },
    (MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read))  => {
      if read then {
        oR = append(oR,xFP(t));
        match (sys_op0,sys_op1,sys_crn,sys_crm,sys_op2) { /* System_Get */
          (3,3,4,2,0)  => iR = RFull("NZCV") :: iR,
          (3,3,4,2,1)  => iR = RFull("DAIF") :: iR,
          (3, 3, 13, 0, 2)  => iR = RFull("TPIDR_EL0") :: iR
        /* TODO FIXME: higher EL TPIDRs */
        }
      } 
      else {
        iR = append(iR,xFP(t));
        match (sys_op0,sys_op1,sys_crn,sys_crm,sys_op2) { /* System_Put */
          (3,3,4,2,0)  => oR = RFull("NZCV") :: oR,
          (3,3,4,2,1)  => oR = RFull("DAIF") :: oR,
          (3, 3, 13, 0, 2)  => oR = RFull("TPIDR_EL0") :: oR
        /* TODO FIXME: higher EL TPIDRs */
        }
      }
    },
    (ImplementationDefinedTestBeginEnd(isEnd))  => (),
    (ImplementationDefinedStopFetching)  => (),
    (ImplementationDefinedThreadStart)  => (),
    (TestBitAndBranch(t,datasize,bit_pos,bit_val,offset))  => {
      iR = append(xFP(t),iR);
      /* TODO: whether the following applies depends on runtime data:
         operand[bit_pos] == bit_val */
      let (i,o) = BranchToFP(iR,oR) in {iR = i; oR = o}; 
      Nias = [| NIAFP_successor, NIAFP_concrete_address(rPC() + offset) |];
      ik = IK_branch;
    },
    (BranchImmediate(branch_type,offset))  => {
      if branch_type == BranchType_CALL
      then {iR = _PCfp :: iR; oR = append(xFP(30),oR)};
      let (i,o) = BranchToFP(iR,oR) in {iR = i; oR = o}; 
      Nias = [| NIAFP_concrete_address(rPC() + offset) |];
      ik = IK_branch
    },
    (BranchRegister(n,branch_type))  => {
      iR = append(iR,xFP(n));
      if branch_type == BranchType_CALL
      then {iR = _PCfp :: iR; oR = append(xFP(30),oR)};
      let (i,o) = BranchToFP(iR,oR) in {iR = i; oR = o};
      Nias = if n ==31
              then [| NIAFP_concrete_address(0) |]
              else [| NIAFP_indirect_address |];
      ik = IK_branch
    },
    (ExceptionReturn)  => not_implemented("ExceptionReturn"),
    (DebugRestorePState)  => not_implemented("DebugRestorePState"),
    (LoadLiteral(t,memop,_signed,size,offset,datasize))  => {
      /* assuming rMem doesn't touch other registers */
      iR = _PCfp :: iR;
      oR = append(xFP(t),oR);
      aR = _PCfp :: aR;
      match memop {
        MemOp_LOAD  => ik = IK_mem_read(Read_plain),
        MemOp_PREFETCH  => {ik = IK_simple; aR = [| |]}
      }
    },
    (LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,datasize))  => {
      rt_unknown : (boolean) = false;
      rn_unknown : (boolean) = false;
      if n==31 then {
        iR = append(CheckSPAlignmentIFP,iR);
        iR = append(rSPIFP,iR);
        aR = append(rSPIFP,aR);
      }
      else if rn_unknown then ()
      else {
        iR = append(xFP(n),iR);
        aR = append(xFP(n),aR);
      };
      match memop {
        MemOp_STORE  => {
          if rt_unknown then ()
          else if pair then iR = append(xFP(t),append(xFP(t2),iR))
          else iR = append(xFP(t),iR);
          if excl then {
            /* TODO: the command below depends on runtime data:
               AArch64_ExclusiveMonitorsPass(address, dbytes) */
            iR = append(iR,wMemIFP);
            oR = append(xFP(s),oR);
            ik = wmem_kind(acctype,true);
          }
          else {
            iR = append(iR,wMemIFP);
            ik = wmem_kind(acctype,false);
          }
        },
        MemOp_LOAD  => {
          if pair then {
            if rt_unknown then
              oR = append(xFP(t),oR)
            else if elsize == 32 then {
              iR = append(iR,BigEndianIFP);
              oR = append(xFP(t),append(xFP(t2),oR));
            }
            else {
              oR = append(xFP(t),append(xFP(t2),oR))
            };
            ik = rmem_kind(acctype,true);
          }
          else {
            oR = append(xFP(t),oR);
            ik = rmem_kind(acctype,excl);
          }
          
        },
        MemOp_PREFETCH  => aR = [| |]
      }
    },
    (LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,datasize,offset))  => {
      rt_unknown : (boolean) = false;
      if n == 31 then {
        iR = append(CheckSPAlignmentIFP,iR);
        iR = append(rSPIFP,iR);
        aR = append(rSPIFP,aR);
      }
      else {
        iR = append(xFP(n),iR);
        aR = append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then
          let (i,o) = wSPFP in {
            iR = append(i,iR);
            oR = append(o,oR);
          }
        else
          oR = append(xFP(n),oR);
      };
      match memop {
        MemOp_STORE  => {
          if rt_unknown & t == n then ()
          else iR = append(xFP(t),iR);
          if rt_unknown & t2 == n then ()
          else iR = append(xFP(t2),iR);
          iR = append(wMemIFP,iR);
          ik = wmem_kind(acctype,false);
        },
        MemOp_LOAD  => {
          oR = append(xFP(t),append(xFP(t2),oR));
          ik = rmem_kind(acctype,false);
        }
      }
    },
    (LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize))  => {
      wb_unknown : (boolean) = false;
      rt_unknown : (boolean) = false;
      if n == 31 then {
        iR = append(CheckSPAlignmentIFP,iR);
        iR = append(rSPIFP,iR);
        aR = append(rSPIFP,aR);
      }
      else {
        iR = append(xFP(n),iR);
        aR = append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then
          let (i,o) = wSPFP in {iR = append(i,iR); oR = append(o,oR)}
        else oR = append(xFP(n),oR);
      };
      match memop {
        MemOp_STORE  => {
          if rt_unknown then ()
          else iR = append(xFP(t),iR);
          iR = append(wMemIFP,iR);
          ik = wmem_kind(acctype,false);
        },
        MemOp_LOAD  => {
          oR = append(xFP(t),oR);
          ik = rmem_kind(acctype,false);
        },
        MemOp_PREFETCH  => aR = [| |]
      }
    },
    (LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize))  => {
      iR = append(xFP(m),iR);
      aR = append(xFP(m),aR);
      wb_unknown : (boolean) = false;
      rt_unknown : (boolean) = false;
      if n == 31 then {
        iR = append(CheckSPAlignmentIFP,iR);
        iR = append(rSPIFP,iR);
        aR = append(rSPIFP,aR);
      }
      else {
        iR = append(xFP(n),iR);
        aR = append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then let (i,o) = wSPFP in {iR = append(i,iR); oR = append(o,oR)}
        else oR = append(xFP(n),oR);
      };
      match memop {
        MemOp_STORE  => {
          if rt_unknown then ()
          else iR = append(xFP(t),iR);
          iR = append(wMemIFP,iR);
          ik = wmem_kind(acctype,false);
        },
        MemOp_LOAD  => {
          oR = append(xFP(t),oR);
          ik = rmem_kind(acctype,false);
        },
        MemOp_PREFETCH  => aR = [| |]
      }
    },
    (LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize,offset))  => {
      rt_unknown : (boolean) = false;
      wb_unknown : (boolean) = false;
      if n == 31 then {
        iR = append(CheckSPAlignmentIFP,iR);
        iR = append(rSPIFP,iR);
        aR = append(rSPIFP,aR);
      }
      else {
        iR = append(xFP(n),iR);
        aR = append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then let (i,o) = wSPFP in {iR = append(i,iR); oR = append(o,oR)}
        else oR = append(xFP(n),oR);
      };
      match memop {
        MemOp_STORE  => {
          if rt_unknown & t == n then ()
          else iR = append(xFP(t),iR);
          if rt_unknown & t2 == n then ()
          else iR = append(xFP(t2),iR);
          iR = append(wMemIFP,iR);
          ik = wmem_kind(acctype,false);
        },
        MemOp_LOAD  => {
          oR = append(xFP(t),oR);
          oR = append(xFP(t2),oR);
          ik = rmem_kind(acctype,false);
        }
      }
    },
    (AddSubImmediate(d,n,datasize,sub_op,setflags,imm))  => {
      iR = append(if n == 31 then rSPIFP else xFP(n),iR);
      if setflags then oR = append(NZCVfp,oR);
      if d ==31 & ~(setflags) then
        let (i,o) = wSPFP in
        { iR = append(i,iR);
          oR = append(o,oR) }
      else oR = append(xFP(d),oR)
    },
    (BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask))  => {
      if inzero then () else iR= append(xFP(d),iR);
      iR = append(xFP(n),iR);
      oR = append(xFP(d),oR);
    },
    (ExtractRegister(d,n,m,datasize,lsb))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      oR = append(xFP(d),oR);
    },
    (LogicalImmediate(d,n,datasize,setflags,op,imm))  => {
      iR = append(xFP(n),iR);
      if setflags then oR = append(NZCVfp,oR);
      if d ==31 & ~(setflags) then let (i,o) = wSPFP in
      { iR = append(i,iR); oR = append(o,oR) }
      else oR = append(xFP(d),oR)
    },
    (MoveWide(d,datasize,imm,pos,opcode))  => {
      if opcode == MoveWideOp_K then iR = append(xFP(d),iR);
      oR = append(xFP(d),oR);
    },
    (Address(d,page,imm))  => {
      iR = _PCfp :: iR;
      oR = append(xFP(d),oR);
    },
    (AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift))  => {
      iR = append(if n == 31 then rSPIFP else xFP(n),iR);
      iR = append(xFP(m),iR);
      if setflags then oR = append(NZCVfp,oR);
      if d ==31 & ~(setflags) then let (i,o) = wSPFP in
      { iR = append(i,iR); oR = append(o,oR) }
      else oR = append(xFP(d),oR)
    },
    (AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      if setflags then oR = append(NZCVfp,oR);
      oR = append(xFP(d),oR);
    },
    (AddSubCarry(d,n,m,datasize,sub_op,setflags))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      iR = PSTATE_Cfp :: iR;
      if setflags then oR = append(NZCVfp,oR);
      oR = append(xFP(d),oR);
    },
    (ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm))  => {
      iR = append(xFP(n),iR);
      iR = append(ConditionHoldsIFP(condition),iR);
      oR = append(NZCVfp,oR);
    },
    (ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      iR = append(ConditionHoldsIFP(condition),iR);
      oR = append(NZCVfp,oR);      
    },
    (ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      iR = append(ConditionHoldsIFP(condition),iR);
      oR = append(xFP(d),oR);
    },
    (Reverse(d,n,datasize,op))  => {
      iR = append(xFP(n),iR);
      oR = append(xFP(d),oR);
    },
    (CountLeading(d,n,datasize,opcode))  => {
      iR = append(xFP(n),iR);
      oR = append(xFP(d),oR);
    },
    (Division(d,n,m,datasize,_unsigned))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      oR = append(xFP(d),oR);
    },
    (Shift(d,n,m,datasize,shift_type))  => {
      iR = append(xFP(m),iR);
      iR = append(xFP(n),iR);
      oR = append(xFP(d),oR);
    },
    (CRC(d,n,m,size,crc32c))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      oR = append(xFP(d),oR);
    },
    (MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op))  => {
      iR = append(xFP(n),iR);
      iR = append(xFP(m),iR);
      iR = append(xFP(a),iR);
      oR = append(xFP(d),oR);
    },
    (MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned))  => {
      iR = append(xFP(n),iR);
      iR = append(xFP(m),iR);
      iR = append(xFP(a),iR);
      oR = append(xFP(d),oR);      
    },
    (MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      oR = append(xFP(d),oR);
    },
    (LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert))  => {
      iR = append(xFP(n),append(xFP(m),iR));
      if setflags then oR = append(NZCVfp,oR);
      oR = append(xFP(d),oR);
    }
  };
  (iR,oR,aR,Nias,Dia,ik)
}
