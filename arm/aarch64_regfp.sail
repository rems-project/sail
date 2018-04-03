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

function instruction_kind rmem_kind ((AccType) acctype, (bool) exclusive) =
  if exclusive then
    switch acctype {
      case AccType_ATOMIC  -> IK_mem_read(Read_exclusive)
      case AccType_ORDERED -> IK_mem_read(Read_exclusive_acquire)
      case _ -> { not_implemented("unimplemented memory access");
                  IK_mem_read(Read_exclusive); }
    }
  else
    switch acctype {
      case AccType_NORMAL  -> IK_mem_read(Read_plain)
      case AccType_ATOMIC  -> IK_mem_read(Read_plain)
      case AccType_STREAM  -> IK_mem_read(Read_stream)
      case AccType_UNPRIV  -> IK_mem_read(Read_plain)
      case AccType_ORDERED -> IK_mem_read(Read_acquire)
    }


function instruction_kind wmem_kind ((AccType) acctype, (bool) exclusive) =
  if exclusive then {
    switch acctype {
      case AccType_ATOMIC  -> IK_mem_write(Write_exclusive)
      case AccType_ORDERED -> IK_mem_write(Write_exclusive_release)
      case _ -> { not_implemented("unimplemented memory access");
                  IK_mem_write(Write_exclusive); }
    }
  } else {
    switch acctype {
      case AccType_NORMAL  -> IK_mem_write(Write_plain)
      case AccType_STREAM  -> IK_mem_write(Write_plain)
      case AccType_UNPRIV  -> IK_mem_write(Write_plain)
      case AccType_ORDERED -> IK_mem_write(Write_release)
      case _ -> { not_implemented("unimplemented memory access");
                  IK_mem_write(Write_plain) }
    };
  }


let (vector<30,31,dec,string>) _Rs =
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

let NZCVfp = [|| PSTATE_Nfp, PSTATE_Zfp, PSTATE_Cfp, PSTATE_Vfp ||]

function regfps xFP((reg_index) n) =
  if n != 31 then [||RFull(_Rs[n])||] else [|| ||]


(* check if this is still what we want *)
function forall Nat 'N, 'N IN {32,64}. (regfps,regfps) BranchToFP (iR,oR) =
  (if UsingAArch32() then iR else PSTATE_ELfp :: iR, _PCfp :: oR)

function regfps ConditionHoldsIFP((bit[4]) _cond) =
  switch _cond[3..1] {
    case 0b000 -> [|| PSTATE_Zfp ||]
    case 0b001 -> [|| PSTATE_Cfp ||]
    case 0b010 -> [|| PSTATE_Nfp ||]
    case 0b011 -> [|| PSTATE_Vfp ||]
    case 0b100 -> [|| PSTATE_Cfp, PSTATE_Zfp ||]
    case 0b101 -> [|| PSTATE_Nfp, PSTATE_Vfp ||]
    case 0b110 -> [|| PSTATE_Nfp, PSTATE_Vfp, PSTATE_Zfp ||]
    case 0b111 -> [|| ||]
  }

(* for iR if rSPFP, for oR if wSPFP *)
let rSPIFP = 
  (* TODO: actually this depends on runtime data: PSTATE_SP and PSTATE_EL *)
  [|| PSTATE_SPfp, RFull("SP_EL0") ||]

let wSPFP = 
  (* TODO: actually this depends on runtime data: PSTATE_SP and PSTATE_EL *)
  ([|| PSTATE_SPfp ||],
   [|| RFull("SP_EL0") ||])


let CheckSPAlignmentIFP = PSTATE_ELfp :: rSPIFP

let BigEndianIFP =
  if UsingAArch32() then [|| RFull("PSTATE_E") ||] else [|| PSTATE_ELfp ||] 

let wMem'IFP = BigEndianIFP 
let wMemIFP = wMem'IFP

function (regfps,regfps,regfps,niafps,diafp,instruction_kind) effect pure initial_analysis (instr) = {
  iR := [|| ||];
  oR := [|| ||];
  aR := [|| ||];
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;
  ik := IK_simple;

  switch instr {
    case (TMStart(t)) -> {
      iR := TxNestingLevelfp :: TXIDR_EL0_DEPTHfp :: iR;
      (* TODO: whether the following applies depends on runtime data:
         ~(TxNestingLevel >= TXIDR_EL0.DEPTH) *)
      oR := TxNestingLevelfp :: append(oR,xFP(t));
      ik := IK_trans(Transaction_start);
    }
    case (TMCommit) -> {
      iR := TxNestingLevelfp :: iR;
      oR := TxNestingLevelfp :: oR;
      ik := IK_trans(Transaction_commit);
    }
    case (TMAbort(retry,reason)) -> {
      iR := TxNestingLevelfp :: iR;
      ik := IK_trans(Transaction_abort);
    }
    case (TMTest) -> {
      iR := TxNestingLevelfp :: iR;
      oR := RFull("NZCV") :: oR;
    }
    case (CompareAndBranch(t,datasize,iszero,offset)) -> {
      iR := append(iR,xFP(t));
      (* TODO: whether the following applies depends on runtime data:
         IsZero(operand1) *)
      let (i,o) = BranchToFP(iR,oR) in {iR := i; oR := o};
      (bit[64]) nia' := rPC() + offset;
      Nias := [|| NIAFP_successor, NIAFP_concrete_address(nia') ||];
      ik := IK_branch;
    }
    case (BranchConditional(offset,condition)) -> {
      iR := append(iR,ConditionHoldsIFP(condition));
      (* TODO: whether the following applies depends on runtime data:
         ConditionHolds(condition) *)
      let (i,o) = BranchToFP(iR,oR) in {iR := i; oR := o};
      Nias := [|| NIAFP_successor, NIAFP_concrete_address(rPC() + offset) ||];
      ik := IK_branch;
    }
    case (GenerateExceptionEL1(imm)) -> not_implemented("GenerateExceptionEL1")
    case (GenerateExceptionEL2(imm)) -> not_implemented("GenerateExceptionEL2")
    case (GenerateExceptionEL3(imm)) -> not_implemented("GenerateExceptionEL3")
    case (DebugBreakpoint(comment)) -> not_implemented("DebugBreakpoint")
    case (ExternalDebugBreakpoint) -> not_implemented("ExternalDebugBreakpoint")
    case (DebugSwitchToExceptionLevel(target_level)) -> not_implemented("DebugSwitchToExceptionLevel")
    case (MoveSystemImmediate(operand,field)) ->
      switch field {
        case PSTATEField_SP -> oR := PSTATE_SPfp :: oR
        case PSTATEField_DAIFSet -> {
          iR := append(iR, [|| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp ||]);
          oR := append(oR, [|| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp ||]);
        }
        case PSTATEField_DAIFClr -> {
          iR := append(iR, [|| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp ||]);
          oR := append(oR, [|| PSTATE_Dfp, PSTATE_Afp, PSTATE_Ifp, PSTATE_Ffp ||]);
        }
      }
    case (Hint(op)) -> 
      switch op {
        case SystemHintOp_YIELD -> ()
        case SystemHintOp_WFE -> {
          if EventRegistered() then () (* ClearEventRegister *)
          else {
            (* the execute code for this case always fails because of
               WaitForEvent, declared as extern but not defined *)
            not_implemented("Hint(SystemHintOp_WFE);") 
          }
        }
        case SystemHintOp_WFI -> {
            (* the execute code for this case always fails because of
               InterruptPending, declared as extern but not defined *)
            not_implemented("Hint(SystemHintOp_WFI);") 
        }
        case SystemHintOp_SEV -> () (*SendEvent*)
        case SystemHintOp_SEVL ->
            (* the execute code for this case always fails because of
               EventRegisterSet, declared as extern but not defined *)
            not_implemented("Hint(SystemHintOp_SEVL);")
        case _ -> () (* do nothing *) 
      }
    case (ClearExclusiveMonitor(imm)) -> () (*ClearExclusiveLocal*)
    case (Barrier(op,domain,types)) -> {
      ik := switch op {
        case MemBarrierOp_DSB ->
          switch types {
            case MBReqTypes_Reads  -> IK_barrier(Barrier_DSB_LD)
            case MBReqTypes_Writes -> IK_barrier(Barrier_DSB_ST)
            case MBReqTypes_All    -> IK_barrier(Barrier_DSB)
          }
        case MemBarrierOp_DMB -> 
          switch types {
            case MBReqTypes_Reads  -> IK_barrier(Barrier_DMB_LD)
            case MBReqTypes_Writes -> IK_barrier(Barrier_DMB_ST)
            case MBReqTypes_All    -> IK_barrier(Barrier_DMB)
          }
        case MemBarrierOp_ISB ->
          IK_barrier(Barrier_ISB)
      };
    }
    case (System(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,has_result)) -> {
      oR := append(oR,xFP(t));
      not_implemented("System"); (* because SysOp_R and SysOp_W *)
    }
    case (MoveSystemRegister(t,sys_op0,sys_op1,sys_op2,sys_crn,sys_crm,read)) -> {
      if read then {
        oR := append(oR,xFP(t));
        switch (sys_op0,sys_op1,sys_crn,sys_crm,sys_op2) { (* System_Get *)
          case (3,3,4,2,0) -> iR := RFull("NZCV") :: iR
          case (3,3,4,2,1) -> iR := RFull("DAIF") :: iR
          case (3, 3, 13, 0, 2) -> iR := RFull("TPIDR_EL0") :: iR
        (* TODO FIXME: higher EL TPIDRs *)
        }
      } 
      else {
        iR := append(iR,xFP(t));
        switch (sys_op0,sys_op1,sys_crn,sys_crm,sys_op2) { (* System_Put *)
          case (3,3,4,2,0) -> oR := RFull("NZCV") :: oR
          case (3,3,4,2,1) -> oR := RFull("DAIF") :: oR
          case (3, 3, 13, 0, 2) -> oR := RFull("TPIDR_EL0") :: oR
        (* TODO FIXME: higher EL TPIDRs *)
        }
      }
    }
    case (ImplementationDefinedTestBeginEnd(isEnd)) -> ()
    case (ImplementationDefinedStopFetching) -> ()
    case (ImplementationDefinedThreadStart) -> ()
    case (TestBitAndBranch(t,datasize,bit_pos,bit_val,offset)) -> {
      iR := append(xFP(t),iR);
      (* TODO: whether the following applies depends on runtime data:
         operand[bit_pos] == bit_val *)
      let (i,o) = BranchToFP(iR,oR) in {iR := i; oR := o}; 
      Nias := [|| NIAFP_successor, NIAFP_concrete_address(rPC() + offset) ||];
      ik := IK_branch;
    }
    case (BranchImmediate(branch_type,offset)) -> {
      if branch_type == BranchType_CALL
        then {iR := _PCfp :: iR; oR := append(xFP(30),oR)};
      let (i,o) = BranchToFP(iR,oR) in {iR := i; oR := o}; 
      Nias := [|| NIAFP_concrete_address(rPC() + offset) ||];
      ik := IK_branch
    }
    case (BranchRegister(n,branch_type)) -> {
      iR := append(iR,xFP(n));
      if branch_type == BranchType_CALL
        then {iR := _PCfp :: iR; oR := append(xFP(30),oR)};
      let (i,o) = BranchToFP(iR,oR) in {iR := i; oR := o};
      Nias := if n ==31
              then [|| NIAFP_concrete_address(0) ||]
              else [|| NIAFP_indirect_address ||];
      ik := IK_branch
    }
    case (ExceptionReturn) -> not_implemented("ExceptionReturn")
    case (DebugRestorePState) -> not_implemented("DebugRestorePState")
    case (LoadLiteral(t,memop,_signed,size,offset,datasize)) -> {
      (* assuming rMem doesn't touch other registers *)
      iR := _PCfp :: iR;
      oR := append(xFP(t),oR);
      aR := _PCfp :: aR;
      switch memop {
        case MemOp_LOAD -> ik := IK_mem_read(Read_plain)
        case MemOp_PREFETCH -> {ik := IK_simple; aR := [|| ||]}
      }
    }
    case (LoadStoreAcqExc(n,t,t2,s,acctype,excl,pair,memop,elsize,regsize,datasize)) -> {
      (boolean) rt_unknown := false;
      (boolean) rn_unknown := false;
      if n==31 then {
        iR := append(CheckSPAlignmentIFP,iR);
        iR := append(rSPIFP,iR);
        aR := append(rSPIFP,aR);
      }
      else if rn_unknown then ()
      else {
        iR := append(xFP(n),iR);
        aR := append(xFP(n),aR);
      };
      switch memop {
        case MemOp_STORE -> {
          if rt_unknown then ()
          else if pair then iR := append(xFP(t),append(xFP(t2),iR))
          else iR := append(xFP(t),iR);
          if excl then {
            (* TODO: the command below depends on runtime data:
               AArch64_ExclusiveMonitorsPass(address, dbytes) *)
            iR := append(iR,wMemIFP);
            oR := append(xFP(s),oR);
            ik := wmem_kind(acctype,true);
          }
          else {
            iR := append(iR,wMemIFP);
            ik := wmem_kind(acctype,false);
          }
        }
        case MemOp_LOAD -> {
          if pair then {
            if rt_unknown then
              oR := append(xFP(t),oR)
            else if elsize == 32 then {
              iR := append(iR,BigEndianIFP);
              oR := append(xFP(t),append(xFP(t2),oR));
            }
            else {
              oR := append(xFP(t),append(xFP(t2),oR))
            };
            ik := rmem_kind(acctype,true);
          }
          else {
            oR := append(xFP(t),oR);
            ik := rmem_kind(acctype,excl);
          }
          
        }
        case MemOp_PREFETCH -> aR := [|| ||]
      }
    }
    case (LoadStorePairNonTemp(wback,postindex,n,t,t2,acctype,memop,scale,datasize,offset)) -> {
      (boolean) rt_unknown := false;
      if n == 31 then {
        iR := append(CheckSPAlignmentIFP,iR);
        iR := append(rSPIFP,iR);
        aR := append(rSPIFP,aR);
      }
      else {
        iR := append(xFP(n),iR);
        aR := append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then
          let (i,o) = wSPFP in {
            iR := append(i,iR);
            oR := append(o,oR);
          }
        else
          oR := append(xFP(n),oR);
      };
      switch memop {
        case MemOp_STORE -> {
          if rt_unknown & t == n then ()
          else iR := append(xFP(t),iR);
          if rt_unknown & t2 == n then ()
          else iR := append(xFP(t2),iR);
          iR := append(wMemIFP,iR);
          ik := wmem_kind(acctype,false);
        }
        case MemOp_LOAD -> {
          oR := append(xFP(t),append(xFP(t2),oR));
          ik := rmem_kind(acctype,false);
        }
      }
    }
    case (LoadImmediate(n,t,acctype,memop,_signed,wback,postindex,offset,regsize,datasize)) -> {
      (boolean) wb_unknown := false;
      (boolean) rt_unknown := false;
      if n == 31 then {
        iR := append(CheckSPAlignmentIFP,iR);
        iR := append(rSPIFP,iR);
        aR := append(rSPIFP,aR);
      }
      else {
        iR := append(xFP(n),iR);
        aR := append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then
          let (i,o) = wSPFP in {iR := append(i,iR); oR := append(o,oR)}
        else oR := append(xFP(n),oR);
      };
      switch memop {
        case MemOp_STORE -> {
          if rt_unknown then ()
          else iR := append(xFP(t),iR);
          iR := append(wMemIFP,iR);
          ik := wmem_kind(acctype,false);
        }
        case MemOp_LOAD -> {
          oR := append(xFP(t),oR);
          ik := rmem_kind(acctype,false);
        }
        case MemOp_PREFETCH -> aR := [|| ||]
      }
    }
    case (LoadRegister(n,t,m,acctype,memop,_signed,wback,postindex,extend_type,shift,regsize,datasize)) -> {
      iR := append(xFP(m),iR);
      aR := append(xFP(m),aR);
      (boolean) wb_unknown := false;
      (boolean) rt_unknown := false;
      if n == 31 then {
        iR := append(CheckSPAlignmentIFP,iR);
        iR := append(rSPIFP,iR);
        aR := append(rSPIFP,aR);
      }
      else {
        iR := append(xFP(n),iR);
        aR := append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then let (i,o) = wSPFP in {iR := append(i,iR); oR := append(o,oR)}
        else oR := append(xFP(n),oR);
      };
      switch memop {
        case MemOp_STORE -> {
          if rt_unknown then ()
          else iR := append(xFP(t),iR);
          iR := append(wMemIFP,iR);
          ik := wmem_kind(acctype,false);
        }
        case MemOp_LOAD -> {
          oR := append(xFP(t),oR);
          ik := rmem_kind(acctype,false);
        }
        case MemOp_PREFETCH -> aR := [|| ||]
      }
    }
    case (LoadStorePair(wback,postindex,n,t,t2,acctype,memop,_signed,datasize,offset)) -> {
      (boolean) rt_unknown := false;
      (boolean) wb_unknown := false;
      if n == 31 then {
        iR := append(CheckSPAlignmentIFP,iR);
        iR := append(rSPIFP,iR);
        aR := append(rSPIFP,aR);
      }
      else {
        iR := append(xFP(n),iR);
        aR := append(xFP(n),aR);
      };
      if wback then {
        if n == 31 then let (i,o) = wSPFP in {iR := append(i,iR); oR := append(o,oR)}
        else oR := append(xFP(n),oR);
      };
      switch memop {
        case MemOp_STORE -> {
          if rt_unknown & t == n then ()
          else iR := append(xFP(t),iR);
          if rt_unknown & t2 == n then ()
          else iR := append(xFP(t2),iR);
          iR := append(wMemIFP,iR);
          ik := wmem_kind(acctype,false);
        }
        case MemOp_LOAD -> {
          oR := append(xFP(t),oR);
          oR := append(xFP(t2),oR);
          ik := rmem_kind(acctype,false);
        }
      }
    }
    case (AddSubImmediate(d,n,datasize,sub_op,setflags,imm)) -> {
      iR := append(if n == 31 then rSPIFP else xFP(n),iR);
      if setflags then oR := append(NZCVfp,oR);
      if d ==31 & ~(setflags) then
        let (i,o) = wSPFP in
        { iR := append(i,iR);
          oR := append(o,oR) }
      else oR := append(xFP(d),oR)
    }
    case (BitfieldMove(d,n,datasize,inzero,extend,R,S,wmask,tmask)) -> {
      if inzero then () else iR:= append(xFP(d),iR);
      iR := append(xFP(n),iR);
      oR := append(xFP(d),oR);
    }
    case (ExtractRegister(d,n,m,datasize,lsb)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      oR := append(xFP(d),oR);
    }
    case (LogicalImmediate(d,n,datasize,setflags,op,imm)) -> {
      iR := append(xFP(n),iR);
      if setflags then oR := append(NZCVfp,oR);
      if d ==31 & ~(setflags) then let (i,o) = wSPFP in
      { iR := append(i,iR); oR := append(o,oR) }
      else oR := append(xFP(d),oR)
    }
    case (MoveWide(d,datasize,imm,pos,opcode)) -> {
      if opcode == MoveWideOp_K then iR := append(xFP(d),iR);
      oR := append(xFP(d),oR);
    }
    case (Address(d,page,imm)) -> {
      iR := _PCfp :: iR;
      oR := append(xFP(d),oR);
    }
    case (AddSubExtendRegister(d,n,m,datasize,sub_op,setflags,extend_type,shift)) -> {
      iR := append(if n == 31 then rSPIFP else xFP(n),iR);
      iR := append(xFP(m),iR);
      if setflags then oR := append(NZCVfp,oR);
      if d ==31 & ~(setflags) then let (i,o) = wSPFP in
      { iR := append(i,iR); oR := append(o,oR) }
      else oR := append(xFP(d),oR)
    }
    case (AddSubShiftedRegister(d,n,m,datasize,sub_op,setflags,shift_type,shift_amount)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      if setflags then oR := append(NZCVfp,oR);
      oR := append(xFP(d),oR);
    }
    case (AddSubCarry(d,n,m,datasize,sub_op,setflags)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      iR := PSTATE_Cfp :: iR;
      if setflags then oR := append(NZCVfp,oR);
      oR := append(xFP(d),oR);
    }
    case (ConditionalCompareImmediate(n,datasize,sub_op,condition,flags,imm)) -> {
      iR := append(xFP(n),iR);
      iR := append(ConditionHoldsIFP(condition),iR);
      oR := append(NZCVfp,oR);
    }
    case (ConditionalCompareRegister(n,m,datasize,sub_op,condition,flags)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      iR := append(ConditionHoldsIFP(condition),iR);
      oR := append(NZCVfp,oR);      
    }
    case (ConditionalSelect(d,n,m,datasize,condition,else_inv,else_inc)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      iR := append(ConditionHoldsIFP(condition),iR);
      oR := append(xFP(d),oR);
    }
    case (Reverse(d,n,datasize,op)) -> {
      iR := append(xFP(n),iR);
      oR := append(xFP(d),oR);
    }
    case (CountLeading(d,n,datasize,opcode)) -> {
      iR := append(xFP(n),iR);
      oR := append(xFP(d),oR);
    }
    case (Division(d,n,m,datasize,_unsigned)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      oR := append(xFP(d),oR);
    }
    case (Shift(d,n,m,datasize,shift_type)) -> {
      iR := append(xFP(m),iR);
      iR := append(xFP(n),iR);
      oR := append(xFP(d),oR);
    }
    case (CRC(d,n,m,size,crc32c)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      oR := append(xFP(d),oR);
    }
    case (MultiplyAddSub(d,n,m,a,destsize,datasize,sub_op)) -> {
      iR := append(xFP(n),iR);
      iR := append(xFP(m),iR);
      iR := append(xFP(a),iR);
      oR := append(xFP(d),oR);
    }
    case (MultiplyAddSubLong(d,n,m,a,destsize,datasize,sub_op,_unsigned)) -> {
      iR := append(xFP(n),iR);
      iR := append(xFP(m),iR);
      iR := append(xFP(a),iR);
      oR := append(xFP(d),oR);      
    }
    case (MultiplyHigh(d,n,m,a,destsize,datasize,_unsigned)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      oR := append(xFP(d),oR);
    }
    case (LogicalShiftedRegister(d,n,m,datasize,setflags,op,shift_type,shift_amount,invert)) -> {
      iR := append(xFP(n),append(xFP(m),iR));
      if setflags then oR := append(NZCVfp,oR);
      oR := append(xFP(d),oR);
    }
  };
  (iR,oR,aR,Nias,Dia,ik)
}
