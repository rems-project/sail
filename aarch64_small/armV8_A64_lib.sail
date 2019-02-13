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

/** FUNCTION:aarch64/exceptions/aborts/AArch64.Abort */

val AArch64_Abort : (bits(64), FaultRecord) -> unit
function AArch64_Abort(vaddress, fault) = {
  not_implemented("AArch64_Abort");
}

/** FUNCTION:AArch64.SPAlignmentFault() */

val AArch64_SPAlignmentFault : unit -> unit effect pure
function AArch64_SPAlignmentFault() = {
  not_implemented("AArch64_SPAlignmentFault");
}

/** FUNCTION:aarch64/exceptions/debug/AArch64.SoftwareBreakpoint */

function AArch64_SoftwareBreakpoint(immediate : bits(16)) -> unit = {
  not_implemented("AArch64_SoftwareBreakpoint");
}

/** FUNCTION:aarch64/exceptions/exceptions/AArch64.TakeReset */

val AArch64_TakeReset : boolean -> unit effect {wreg}
function AArch64_TakeReset(cold_reset) = {
  assert((~(HighestELUsingAArch32())), None);

  /* Enter the highest implemented Exception level in AArch64 state */
  PSTATE_nRW = 0;
  if HaveEL(EL3) then {
    PSTATE_EL = EL3;
    SCR_EL3.NS = 0; /* Secure state */
  } else if HaveEL(EL2) then
    PSTATE_EL = EL2
  else
    PSTATE_EL = EL1;

  /* Reset the system registers and other system components */
  AArch64_ResetControlRegisters(cold_reset);

  /* Reset all other PSTATE fields */
  PSTATE_SP = 0;           /* Select stack pointer               */
  wPSTATE_DAIF() = 0b1111; /* All asynchronous exceptions masked */
  PSTATE_SS = 0;           /* Clear software step bit            */
  PSTATE_IL = 0;           /* Clear illegal execution state bit  */

  /* All registers, bits and fields not reset by the above pseudocode or by the BranchTo() call */
  /* below are UNKNOWN bitstrings after reset. In particular, the return information registers  */
  /* ELR_ELx and SPSR_ELx have UNKNOWN values, so that it is impossible to return from a reset  */
  /* in an architecturally defined way.                                                         */
  AArch64_ResetGeneralRegisters();
  AArch64_ResetSIMDFPRegisters();
  AArch64_ResetSpecialRegisters();
  ResetExternalDebugRegisters(cold_reset);

  rv : bits(64) = 0; /* ARM: uninitialized */ /* IMPLEMENTATION DEFINED reset vector */
  if HaveEL(EL3) then
    rv = RVBAR_EL3
  else if HaveEL(EL2) then
    rv = RVBAR_EL2
  else
    rv = RVBAR_EL1;

  /* The reset vector must be correctly aligned */
  assert((IsZero(rv[63..(PAMax())]) & IsZero(rv[1..0])), Some("reset vector not correctly aligned"));

  BranchTo(rv, BranchType_UNKNOWN);
}

/** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallHypervisor */

val AArch64_CallHypervisor : immediate -> unit 
function AArch64_CallHypervisor (immediate) = {
  not_implemented("AArch64_CallHypervisor");
}

/** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallSecureMonitor */

val AArch64_CallSecureMonitor : bits(16) -> unit
function AArch64_CallSecureMonitor(immediate) = {
  not_implemented("AArch64_CallSecureMonitor");
}

/** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallSupervisor */

val AArch64_CallSupervisor : bits(16) -> unit
function AArch64_CallSupervisor(immediate) = {
  not_implemented("AArch64_CallSupervisor");
}

/** FUNCTION:aarch64/exceptions/traps/AArch64.CheckForSMCTrap */

val AArch64_CheckForSMCTrap : bits(16) -> unit
function AArch64_CheckForSMCTrap(imm) = {
  route_to_el2 : boolean = (HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL == EL0 | PSTATE_EL == EL1) & HCR_EL2.TSC == 1);
  if route_to_el2 then {
    not_implemented("AArch64_CheckForSMCTrap route_to_el2");
    /* ARM:
    bits(64) preferred_exception_return = ThisInstrAddr();
    vect_offset = 0x0;
    exception = ExceptionSyndrome(Exception_MonitorCall);
    exception.syndrome<15:0> = imm;
    AArch64.TakeException(EL2, exception, preferred_exception_return, vect_offset);
    */
  };
}

/** FUNCTION:aarch64/exceptions/traps/AArch64.CheckForWFxTrap */

val AArch64_CheckForWFxTrap : (bits(2), boolean) -> unit effect{rreg}
function AArch64_CheckForWFxTrap(target_el, is_wfe) = {
    assert((HaveEL(target_el)), None);

    trap : boolean = false; /* ARM: uninitialized */

    if      target_el == EL1 then trap = ((if is_wfe then SCTLR_EL1.nTWE else SCTLR_EL1.nTWI) == 0)
    else if target_el == EL2 then trap = ((if is_wfe then HCR_EL2.TWE else HCR_EL2.TWI) == 1)
    else if target_el == EL3 then trap = ((if is_wfe then SCR_EL3.TWE else SCR_EL3.TWI) == 1)
    else {assert(false,None); ()};


    if trap then
        AArch64_WFxTrap(target_el, is_wfe);
}

/** FUNCTION:aarch64/exceptions/traps/AArch64.SystemRegisterTrap */

function AArch64_SystemRegisterTrap(
            target_el : bits(2), op0 : bits(2), op2 : bits(3), op1 : bits(3), 
            crn : bits(4), rt : bits(5), crm : bits(4), dir : bit) -> unit = {
  not_implemented("AArch64_SystemRegisterTrap");
}

/** FUNCTION:aarch64/exceptions/traps/AArch64.UndefinedFault */

function AArch64_UndefinedFault() -> unit = {
  not_implemented("AArch64_UndefinedFault");
}

/** FUNCTION:aarch64/exceptions/traps/AArch64.WFxTrap */

function AArch64_WFxTrap(target_el : bits(2), is_wfe : boolean) -> unit = {
  not_implemented("AArch64_WFxTrap");
}

/** FUNCTION:aarch64/functions/aborts/AArch64.CreateFaultRecord */

function AArch64_CreateFaultRecord(
           faulttype : Fault, ipaddress : bits(48), level : uinteger, acctype : AccType, 
           write : boolean, extflag : bit, secondstage : boolean, s2fs1walk : boolean) -> FaultRecord = {
  fault : FaultRecord = {
    faulttype = faulttype;
    domain = UNKNOWN : bits(4);
    debugmoe = UNKNOWN : bits(4);
    ipaddress = ipaddress;
    level = level;
    acctype = acctype;
    write = write;
    extflag = extflag;
    secondstage = secondstage;
    s2fs1walk = s2fs1walk;
  };

  fault;
}

/** FUNCTION:aarch64/functions/exclusive/AArch64.ExclusiveMonitorsPass */

function AArch64_ExclusiveMonitorsPass(address : bits(64), size : uinteger) -> boolean = {
  /*It is IMPLEMENTATION DEFINED whether the detection of memory aborts happens*/
  /*before or after the check on the local Exclusive Monitor. As a result a failure*/
  /*of the local monitor can occur on some implementations even if the memory*/
  /*access would give an memory abort.*/

  acctype : AccType = AccType_ATOMIC;
  iswrite : boolean = true;
  aligned : boolean = (address == Align(address, size));

  if ~(aligned) then {
    secondstage : boolean = false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
  };

  passed : boolean = AArch64_IsExclusiveVA(address, ProcessorID(), size);
  if ~(passed) then
    /* return */ false
  else {

  memaddrdesc : AddressDescriptor = 
    AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);

  /*Check for aborts or debug exceptions*/
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  passed = IsExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);

  if passed then {
      ClearExclusiveLocal(ProcessorID());
      if (memaddrdesc.memattrs).shareable then
          passed = IsExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size);
  };

  passed;
}}

/** FUNCTION:aarch64/functions/exclusive/AArch64.IsExclusiveVA */

function AArch64_IsExclusiveVA(address : bits(64), processorid : integer, size : uinteger) -> boolean = {
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

/** FUNCTION:aarch64/functions/exclusive/AArch64.MarkExclusiveVA */

val AArch64_MarkExclusiveVA : (bits(64), integer, uinteger) -> unit effect pure
function AArch64_MarkExclusiveVA (address, processorid, size) = {
  info("The model does not implement the exclusive monitors explicitly.");
}

/** FUNCTION:aarch64/functions/exclusive/AArch64.SetExclusiveMonitors */

function AArch64_SetExclusiveMonitors(address : bits(64), size : uinteger) -> unit = {
  acctype : AccType = AccType_ATOMIC;
  iswrite : boolean = false;
  aligned : boolean = (address != Align(address, size));

  memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);

  /* Check for aborts or debug exceptions */
  if IsFault(memaddrdesc) then
    /* return */ ()
  else {

  if (memaddrdesc.memattrs).shareable then
    MarkExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size);

  MarkExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);

  AArch64_MarkExclusiveVA(address, ProcessorID(), size);
}}

/** FUNCTION:aarch64/functions/memory/AArch64.CheckAlignment */

function AArch64_CheckAlignment(address : bits(64), size : uinteger, 
                                acctype : AccType, iswrite : boolean) -> boolean = {
  aligned : boolean = (address == Align(address, size));
  A : bit = (SCTLR'()).A;

  if ~(aligned) & (acctype == AccType_ATOMIC | acctype == AccType_ORDERED | A == 1) then {
    secondstage = false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
  };

  aligned;
}

/** FUNCTION:// AArch64.MemSingle[] - non-assignment (read) form */

val AArch64_rMemSingle : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, bits(64), atom('N), AccType, boolean, bool) -> read_buffer_type effect {rmem}
function AArch64_rMemSingle (read_buffer, address, size, acctype, wasaligned, exclusive) = {
  /*assert size IN {1, 2, 4, 8, 16};*/
  assert((address == Align(address, size)), None);

  /* ARM: AddressDescriptor memaddrdesc; */
  value : bits('N*8) = 0;
  iswrite : boolean = false;

  /* MMU or MPU */
  memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size);

  /* Check for aborts or debug exceptions */
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  /* Memory array access */
  _rMem(read_buffer, memaddrdesc, size, acctype, exclusive);
}

/** FUNCTION:// AArch64.MemSingle[] - assignment (write) form */

val AArch64_wMemSingle : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, bits(64), atom('N), AccType, boolean, bool, bits('N*8)) -> write_buffer_type effect pure
function AArch64_wMemSingle (write_buffer, address, size, acctype, wasaligned, exclusive, value) = {
  /*assert size IN {1, 2, 4, 8, 16};*/
  assert((address == Align(address, size)), None);

  /* ARM: AddressDescriptor memaddrdesc; */
  iswrite : boolean = true;

  /* MMU or MPU */
  memaddrdesc : AddressDescriptor = AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size);

  /* Check for aborts or debug exceptions */
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  /* Effect on exclusives */
  if (memaddrdesc.memattrs).shareable then
    ClearExclusiveByAddress(memaddrdesc.paddress, ProcessorID(), size);

  /* Memory array access */
  _wMem(write_buffer, memaddrdesc, size, acctype, exclusive, value)
}

/** FUNCTION:CheckSPAlignment() */

val CheckSPAlignment : unit -> unit effect {rreg}
function CheckSPAlignment() = {
    sp : bits(64) = rSP();
    stack_align_check : bool = false; /* ARM: this is missing from ARM ARM */

    if PSTATE_EL == EL0 then
        stack_align_check = (SCTLR_EL1.SA0 != 0)
    else
        stack_align_check = ((SCTLR'()).SA != 0);

    if stack_align_check & sp != Align(sp, 16) then
        AArch64_SPAlignmentFault();
}

/** FUNCTION://   Mem[] - non-assignment (read) form */

val rMem' : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, bits(64),atom('N), AccType, bool) -> read_buffer_type effect {rmem}
function rMem'(read_buffer, address, size, acctype, exclusive) =
{
  /* ARM: assert size IN {1, 2, 4, 8, 16}; */
  read_buffer' : read_buffer_type = read_buffer;

  i : uinteger = 0; /* ARM: uninitialized */
  iswrite : boolean = false;

  aligned : boolean = AArch64_CheckAlignment(address, size, acctype, iswrite);
  atomic : boolean = ((aligned & ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM)) | size == 1);

  if ~(atomic) then {
    assert((~(exclusive)), None); /* as far as I can tell this should never happen */

    assert((size > 1), None);
    if (~(exclusive)) then {
     /*value[7..0] =*/read_buffer' =  AArch64_rMemSingle(read_buffer', address, 1, acctype, aligned, false);

    /* For subsequent bytes it is CONSTRAINED UNPREDICTABLE whether an unaligned Device memory */
    /* access will generate an Alignment Fault, as to get this far means the first byte did    */
    /* not, so we must be changing to a new translation page.                                  */
    /* FIXME: ???
    if ~(aligned) then {
      c = ConstrainUnpredictable();
      assert c IN {Constraint_FAULT, Constraint_NONE};
      if c == Constraint_NONE then aligned = TRUE;
    };*/

    foreach (i from 1 to (size - 1)) {
      /*value[(8*i+7)..(8*i)] =*/read_buffer' = AArch64_rMemSingle(read_buffer', address+i, 1, acctype, aligned, false);
  }}} else 
    /*value =*/read_buffer' = AArch64_rMemSingle(read_buffer', address, size, acctype, aligned, exclusive);

  /*if BigEndian() then
    value = BigEndianReverse(value);
  value;*/
  read_buffer'
}

val rMem : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, bits(64), atom('N), AccType) -> read_buffer_type effect {rmem}
function rMem (read_buffer, address, size, acctype) =
  rMem'(read_buffer, address, size, acctype, false)

val rMem_exclusive : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, bits(64), atom('N), AccType) -> read_buffer_type effect {rmem}
function rMem_exclusive(read_buffer, address, size, acctype) =
  rMem'(read_buffer, address, size, acctype, true)

/** FUNCTION:// Mem[] - assignment (write) form */

/* the 'exclusive' and return value are our addition for handling
   store-exclusive, this function should only be called indirectly by one
   of the functions that follow it.
   returns true if the store-exclusive was successful. */
val wMem' : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, bits(64), atom('N), AccType, bits('N*8), bool) -> write_buffer_type 
function wMem' (write_buffer, address, size, acctype, value, exclusive) = {
  write_buffer' : write_buffer_type = write_buffer;

  /* sail doesn't allow assignment to function arguments */
  value' : bits('N*8) = value; 

  i : uinteger = 0; /* ARM: uninitialized */
  iswrite : boolean = true;

  if BigEndian() then
    value' = BigEndianReverse(value');
  aligned : boolean = AArch64_CheckAlignment(address, size, acctype, iswrite);
  atomic : boolean = ((aligned & ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM)) | size == 1);

  exclusiveSuccess : bool = false;
  if ~(atomic) then {
    assert((~(exclusive)), None); /* as far as I can tell this should never happen */

    if (~(exclusive)) then {
    assert((size > 1), None);
    write_buffer' = AArch64_wMemSingle(write_buffer', address, 1, acctype, aligned, false, value'[7..0]);

    /* For subsequent bytes it is CONSTRAINED UNPREDICTABLE whether an unaligned Device memory */
    /* access will generate an Alignment Fault, as to get this far means the first byte did    */
    /* not, so we must be changing to a new translation page.                                  */
    /* FIXME:
    if !aligned then
      c = ConstrainUnpredictable();
      assert c IN {Constraint_FAULT, Constraint_NONE};
      if c == Constraint_NONE then aligned = TRUE;*/

    foreach (i from 1 to (size - 1))
      write_buffer' = AArch64_wMemSingle(write_buffer', address+i, 1, acctype, aligned, false, value'[(8*i+7)..(8*i)]);
  }} else
      write_buffer' = AArch64_wMemSingle(write_buffer', address, size, acctype, aligned, exclusive, value');

  write_buffer'
}

val wMem : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, bits(64), atom('N), AccType, bits('N*8)) -> write_buffer_type
function wMem (write_buffer, address, size, acctype, value) =
  wMem'(write_buffer, address, size, acctype, value, false)

val wMem_exclusive : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, bits(64), atom('N), AccType, bits('N*8)) -> buffer_type 
function wMem_exclusive(write_buffer, address, size, acctype, value) =
  wMem'(write_buffer, address, size, acctype, value, true)

/** FUNCTION:aarch64/functions/registers/AArch64.ResetGeneralRegisters */

function unit AArch64_ResetGeneralRegisters() =
{
  foreach (i from 0 to 30)
    wX(i) = (UNKNOWN : bits(64));
}

/** FUNCTION:aarch64/functions/registers/AArch64.ResetSIMDFPRegisters */

function unit AArch64_ResetSIMDFPRegisters() =
{
  foreach (i from 0 to 31)
    wV(i) = (UNKNOWN : bits(128));
}

/** FUNCTION:aarch64/functions/registers/AArch64.ResetSpecialRegisters */

function unit AArch64_ResetSpecialRegisters() =
{
  /* AArch64 special registers */
  SP_EL0 = (UNKNOWN : bits(64));
  SP_EL1 = (UNKNOWN : bits(64));
  SPSR_EL1 = (UNKNOWN : bits(32));
  ELR_EL1 = (UNKNOWN : bits(64));
  if HaveEL(EL2) then {
    SP_EL2 = (UNKNOWN : bits(64));
    SPSR_EL2 = (UNKNOWN : bits(32));
    ELR_EL2 = (UNKNOWN : bits(64));
  };
  if HaveEL(EL3) then {
    SP_EL3 = (UNKNOWN : bits(64));
    SPSR_EL3 = (UNKNOWN : bits(32));
    ELR_EL3 = (UNKNOWN : bits(64));
  };

  /* AArch32 special registers that are not architecturally mapped to AArch64 registers */
  if HaveAArch32EL(EL1) then {
    SPSR_fiq = (UNKNOWN : bits(32));
    SPSR_irq = (UNKNOWN : bits(32));
    SPSR_abt = (UNKNOWN : bits(32));
    SPSR_und = (UNKNOWN : bits(32));
  };

  /* External debug special registers */
  DLR_EL0 = (UNKNOWN : bits(64));
  DSPSR_EL0 = (UNKNOWN : bits(32));
}

/** FUNCTION:aarch64/functions/registers/PC */

val rPC : unit -> bits(64) effect {rreg}
function rPC () = _PC

/** FUNCTION:// SP[] - assignment form */

val wSP : forall 'N, 'N in {32,64}. (unit, bits('N)) -> unit effect {rreg,wreg}
function wSP ((), value) = {
  /*assert width IN {32,64};*/
  if PSTATE_SP == 0 then
    SP_EL0 = ZeroExtend(value)
  else
    let pstate_el = PSTATE_EL in {
      if      pstate_el == EL0 then SP_EL0 = ZeroExtend(value)
      else if pstate_el == EL1 then SP_EL1 = ZeroExtend(value)
      else if pstate_el == EL2 then SP_EL2 = ZeroExtend(value)
      else if pstate_el == EL3 then SP_EL3 = ZeroExtend(value)
      else assert(false,None); ();
    }
}

/** FUNCTION:// SP[] - non-assignment form */

val rSP : unit -> bits('N) effect {rreg}
function rSP () = {
  /*assert width IN {8,16,32,64};*/
  if PSTATE_SP == 0 then
    mask(SP_EL0)
  else
    let pstate_el = PSTATE_EL in {
      if      pstate_el == EL0 then mask(SP_EL0)
      else if pstate_el == EL1 then mask(SP_EL1)
      else if pstate_el == EL2 then mask(SP_EL2)
      else if pstate_el == EL3 then mask(SP_EL3)
      else {assert(false,None); mask(SP_EL3)}
    }
}

/** FUNCTION://   V[] - assignment form */

val wV : forall 'N, 'N in {8,16,32,64,128}. (SIMD_index, bits('N)) -> unit effect {wreg}
function wV (n, value) = {
  /*assert n >= 0 && n <= 31;*/
  /*assert width IN {8,16,32,64,128};*/
  _V[n] = ZeroExtend(value);
}

/** FUNCTION://   V[] - non-assignment form */

val rV: forall 'N, 'N in {8,16,32,64,128}. SIMD_index -> bits('N) effect {rreg}
function rV (n) = mask(_V[n])


/** FUNCTION:// Vpart[] - non-assignment form */

val rVpart : forall 'N, 'N in {8,16,32,64,128}. (SIMD_index, range(0,1)) -> bits('N) effect {rreg}
function rVpart (n,part) = {
  if part == 0 then
    mask(_V[n]) : bits('N)
  else {
    assert((length(0 : bits('N)) == 64), None);
    ((_V[n])[127..64]) : bits(64);
  }
}

/** FUNCTION:// Vpart[] - assignment form */

val wVpart : forall 'N, 'N in {8,16,32,64,128}. (SIMD_index, range(0,1), bits('N)) -> unit effect {wreg}
function wVpart(n, part, value) = {
  if part == 0 then
    _V[n] = ZeroExtend(value)
  else {
    assert((length(0 : bits('N)) == 64), None);
    (_V[n])[127..64] = value;
  }
}

/** FUNCTION:// X[] - assignment form */

val wX : forall 'N, 'N in {32,64}. (reg_index, bits('N)) -> unit effect {wreg}
function wX(n, value) = {
  /*assert n >= 0 && n <= 31;*/
  /*assert width IN {32,64};*/
  if n != 31 then
    _R[n] = ZeroExtend(value);
}

/** FUNCTION:// X[] - non-assignment form */

val rX : forall 'N, 'N in {8,16,32,64}. reg_index -> bits('N) effect {rreg}
function rX(n) = {
  /*assert n >= 0 && n <= 31;*/
  /*assert width IN {8,16,32,64};*/
  if n != 31 then
    mask(_R[n])
  else
    Zeros();
}

/** FUNCTION:bits(64) ELR[bits(2) el] */

function rELR(el : bits(2)) -> bits(64) = {
  r = 0 : bits(64); /* ARM: uninitialized */
  if      el == EL1 then r = ELR_EL1
  else if el == EL2 then r = ELR_EL2
  else if el == EL3 then r = ELR_EL3
  else Unreachable();
  r;
}

/** FUNCTION:bits(64) ELR[] */

function rELR'() -> bits(64) =
{
    assert (PSTATE_EL != EL0, None);
    rELR(PSTATE_EL);
}

/** FUNCTION:SCTLRType SCTLR[bits(2) regime] */

val SCTLR : bits(2) -> SCTLR_type effect {rreg}
function SCTLR (regime) = {
   if      regime == EL1 then SCTLR_EL1
   else if regime == EL2 then SCTLR_EL2
   else if regime == EL3 then SCTLR_EL3
   else {assert(false,Some("SCTLR_type unreachable")); SCTLR_EL1} /* ARM: Unreachabe() */
}

/** FUNCTION:SCTLRType SCTLR[] */

val SCTLR' : unit -> SCTLR_type effect{rreg}
function SCTLR' () = SCTLR(S1TranslationRegime())

/** FUNCTION:aarch64/functions/system/AArch64.CheckUnallocatedSystemAccess */

/* return true if the access is not allowed */
function AArch64_CheckUnallocatedSystemAccess (op0 : bits(2), op1 : bits(3), crn : bits(4), 
                                               crm : bits(4), op2 : bits(3), read : bit) -> boolean =
{
  match (op0,op1,crn,crm,op2, read) {
    (0b00,0b000,0b0100,_,0b101, _)  => PSTATE_EL < EL1 /* SPSel */,
    (0b00,0b011,0b0100,_,0b110, _)  => false, /* DAIFSet */ /* TODO: EL0 Config-RW ??? */
    (0b00,0b011,0b0100,_,0b111, _)  => false, /* DAIFClr */ /* TODO: EL0 Config-RW ??? */

    /* follow the "Usage constraints" of each register */
    (0b11,0b011,0b0100,0b0010,0b000, _)  => false, /* NZCV */
    (0b11,0b011,0b0100,0b0010,0b001, _)  => false /* DAIF */ /* TODO: EL0 Config-RW ??? */
/*     (0b11,0b000,0b0001,0b0000,0b001, _)  => PSTATE_EL < EL1 /* ACTLR_EL1 */ */
  }
}

/** FUNCTION:aarch64/functions/system/CheckSystemAccess */

function CheckSystemAccess (op0 : bits(2), op1 : bits(3), crn : bits(4), crm : bits(4), 
                            op2 : bits(3), rt : bits(5), read : bit) -> unit =
{
  /*Checks if an AArch64 MSR/MRS/SYS instruction is UNALLOCATED or trapped at the current exception*/
  /*level, security state and configuration, based on the opcode's encoding.*/
  unallocated : boolean = false;
  need_secure : boolean = false;
  min_EL : bits(2) = 0; /* ARM: uninitialized */

  /*Check for traps by HCR_EL2.TIDCP*/
  /* TODO: uncomment when implementing traps
  if HaveEL(EL2) & ~(IsSecure()) & HCR_EL2.TIDCP == 1 & op0[0] == 1 & (switch crn {[1,_,1,1] -> true case _  => false}) then {
    /*At Non-secure EL0, it is IMPLEMENTATION_DEFINED whether attempts to execute system control*/
    /*register access instructions with reserved encodings are trapped to EL2 or UNDEFINED*/
    if PSTATE_EL == EL0 /* FIXME: & boolean IMPLEMENTATION_DEFINED "Reserved Control Space EL0 Trapped" */ then
      AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read)
    else if PSTATE.EL == EL1 then
      AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read);
  };*/

  /*Check for unallocated encodings*/
  match op1 {
    (0b00@[_])  =>
      min_EL = EL1,
    0b010  =>
      min_EL = EL1,
    0b011  =>
      min_EL = EL0,
    0b100  =>
      min_EL = EL2,
    0b101  =>
      UnallocatedEncoding(),
    0b110  =>
      min_EL = EL3,
    0b111  => {
      min_EL = EL1;
      need_secure = true;
    }
  };
  if PSTATE_EL < min_EL then /* ARM: UInt */
      UnallocatedEncoding()
  else if need_secure & ~(IsSecure()) then
      UnallocatedEncoding()
  else if AArch64_CheckUnallocatedSystemAccess(op0, op1, crn, crm, op2, read) then
      UnallocatedEncoding();
  /*Check for traps on accesses to SIMD or floating-point registers*/
  /* TODO: uncomment when implementing SIMD/FP
  let AArch64 : take_trap, target_el.CheckAdvSIMDFPSystemRegisterTraps(op0, op1, crn, crm, op2) in {
    if take_trap then
      AArch64_AdvSIMDFPAccessTrap(target_el);
  };*/

  /*Check for traps on access to all other system registers*/
  /* TODO: uncomment when implementing traps
  let AArch64_CheckSystemRegisterTraps : take_trap, target_el(op0, op1, crn, crm, op2, read) in {
    if take_trap then
        AArch64_SystemRegisterTrap(target_el, op0, op2, op1, crn, rt, crm, read);
  };*/
}

/** FUNCTION:aarch64/functions/system/SysOp_R */

val SysOp_R : (uinteger, uinteger, uinteger, uinteger, uinteger) -> bits(64)
function SysOp_R(op0, op1, crn, crm, op2) = {
  not_implemented("SysOp_R");
  0;
}

/** FUNCTION:aarch64/functions/system/SysOp_W */

val SysOp_W : (uinteger, uinteger, uinteger, uinteger, uinteger, bits(64)) -> unit
function unit SysOp_W(op0, op1, crn, crm, op2, _val) = {
  not_implemented("SysOp_W");
}

/** FUNCTION:bits(64) System_Get(integer op0, integer op1, integer crn, integer crm, integer op2); */

val System_Get : (uinteger, uinteger, uinteger, uinteger, uinteger) -> bits(64) 
function System_Get(op0, op1, crn, crm, op2) -> bits(64) = {
  match (op0,op1,crn,crm,op2) {
    (3,3,4,2,0)  => ZeroExtend(NZCV),
    (3,3,4,2,1)  => ZeroExtend(DAIF),
    (3, 3, 13, 0, 2)  => TPIDR_EL0
  /* TODO FIXME: higher EL TPIDRs */

/*     (3,0,1,0,1)  => ZeroExtend(ACTLR_EL1) */
  }
}

/** FUNCTION:System_Put(integer op0, integer op1, integer crn, integer crm, integer op2, bits(64) val); */

val System_Put : (uinteger, uinteger, uinteger, uinteger, uinteger, bits(64)) -> unit effect {wreg}
function System_Put(op0, op1, crn, crm, op2, _val) = {
  match (op0,op1,crn,crm,op2) {
    (3,3,4,2,0)   => NZCV = _val[31..0],
    (3,3,4,2,1)   => DAIF = _val[31..0],
    (3,3,13,0,2)  => TPIDR_EL0 = _val[63..0]
  /* TODO FIXME: higher EL TPIDRs */

/*     (3,0,1,0,1)  => ACTLR_EL1 = _val[31..0] */
  }
}

/** FUNCTION:aarch64/instrs/branch/eret/AArch64.ExceptionReturn */

function unit AArch64_ExceptionReturn(new_pc : bits(64), spsr : bits(32)) = {
  not_implemented("AArch64_ExceptionReturn");
}

/** ENUMERATE:aarch64/instrs/countop/CountOp */
/** FUNCTION:ExtendType DecodeRegExtend(bits(3) op) */

function ExtendType DecodeRegExtend (op : bits(3)) = {
  match op {
    0b000  => ExtendType_UXTB,
    0b001  => ExtendType_UXTH,
    0b010  => ExtendType_UXTW,
    0b011  => ExtendType_UXTX,
    0b100  => ExtendType_SXTB,
    0b101  => ExtendType_SXTH,
    0b110  => ExtendType_SXTW,
    0b111  => ExtendType_SXTX
  }
}

/** FUNCTION:aarch64/instrs/extendreg/ExtendReg */

val ExtendReg : forall 'N 'S, 'N in {8,16,32,64} & 'S >= 0 & 'S <= 4.
    (implicit('N), reg_index, ExtendType, atom('S)) -> bits('N) effect {rreg} 
function ExtendReg (_reg, etype, shift) =
{
  /*assert( shift >= 0 & shift <= 4 );*/
   /* _val */ rX : bits('N) = (_reg);
  _unsigned : boolean = false;
  len : uinteger = 0;

  match etype {
    ExtendType_SXTB  => { _unsigned = false; len = 8 },
    ExtendType_SXTH  => { _unsigned = false; len = 16},
    ExtendType_SXTW  => { _unsigned = false; len = 32},
    ExtendType_SXTX  => { _unsigned = false; len = 64},
    ExtendType_UXTB  => { _unsigned = true;  len = 8 },
    ExtendType_UXTH  => { _unsigned = true;  len = 16},
    ExtendType_UXTW  => { _unsigned = true;  len = 32},
    ExtendType_UXTX  => { _unsigned = true;  len = 64}
  };

  len = uMin(len, length(_val) - shift);
  Extend((_val[(len - 1)..0]) @ (Zeros() : bits('S)), _unsigned)
}

/** ENUMERATE:aarch64/instrs/extendreg/ExtendType */
/** ENUMERATE:aarch64/instrs/integer/arithmetic/rev/revop/RevOp */
/** FUNCTION:(bits(M), bits(M)) DecodeBitMasks (bit immN, bits(6) imms, bits(6) immr, boolean immediate) */

val DecodeBitMasks : forall 'M 'E, 'M >= 0 & 'E in {2,4,8,16,32,64}. (implicit('M),bit,bits(6),bits(6),boolean) -> (bits('M),bits('M)) effect {escape}
function DecodeBitMasks(immN, imms, immr, immediate) = {
  let M = (length(0 : bits('M))) in {
/* ARM: (bits('M)) tmask = 0; /* ARM: uninitialized */ */
/* ARM: (bits('M)) wmask = 0; /* ARM: uninitialized */ */
  levels : bits(6) = 0; /* ARM: uninitialized */

  /* Compute log2 of element size */
  /* 2^len must be in range [2, 'M] */
  len : range(0,6) = match HighestSetBit([immN]@(NOT(imms))) {
    None  => { assert (false,Some("DecodeBitMasks: HighestSetBit returned None")); 0; },
    (Some(c))  => c
  };
  if len < 1 then ReservedValue();
  assert((M >= lsl(1, len)),None);

  /* Determine S, R and S - R parameters */
  levels = ZeroExtend(0b1 ^^ len);

  /* For logical immediates an all-ones value of S is reserved */
  /* since it would generate a useless all-ones result (many times) */
  if immediate & ((imms & levels) == levels) then
    ReservedValue();

  S : bits(6) = (imms & levels);
  R : bits(6) = (immr & levels);
  diff : bits(6) = S - R; /* 6-bit subtract with borrow */

  esize : atom('E) = lsl(1, len);
  d : bits(6) = diff[(len - 1)..0];
  welem : bits('E) = ZeroExtend(0b1 ^^ (S + 1));
  telem : bits('E) = ZeroExtend(0b1 ^^ (d + 1));
  wmask = Replicate(ROR(welem, R));
  tmask = Replicate(telem);
  (wmask, tmask);
}}

/** ENUMERATE:aarch64/instrs/integer/ins-ext/insert/movewide/movewideop/MoveWideOp */
/** FUNCTION:ShiftType DecodeShift(bits(2) op) */

function ShiftType DecodeShift(op : bits(2)) = op : range(0,4)

/** FUNCTION:bits(N) ShiftReg(integer reg, ShiftType type, integer amount) */

val ShiftReg : forall 'N, 'N >= 0. (implicit('N), reg_index, ShiftType, nat) -> bits('N) effect {rreg}
function ShiftReg(_reg, stype, amount) = {
  result : bits('N) = rX(_reg);
  match stype {
    ShiftType_LSL  => result = LSL(result, amount),
    ShiftType_LSR  => result = LSR(result, amount),
    ShiftType_ASR  => result = ASR(result, amount),
    ShiftType_ROR  => result = ROR(result, amount)
  };
  result;
}

/** ENUMERATE:aarch64/instrs/integer/shiftreg/ShiftType */
/** ENUMERATE:aarch64/instrs/logicalop/LogicalOp */
/** ENUMERATE:aarch64/instrs/memory/memop/MemOp */
/** FUNCTION:aarch64/instrs/memory/prefetch/Prefetch */

function unit Prefetch(address : bits(64), prfop : bits(5)) = {
  hint : PrefetchHint = 0;
  target : uinteger = 0;
  stream : boolean = 0;

  returnv : bool = false;
  match prfop[4..3] {
    0b00  => hint = Prefetch_READ,  /* PLD: prefetch for load    */
    0b01  => hint = Prefetch_EXEC,  /* PLI: preload instructions */
    0b10  => hint = Prefetch_WRITE, /* PST: prepare for store    */
    0b11  => returnv = true         /* unallocated hint          */
  };
  if ~(returnv) then {
  target = prfop[2..1];                /* target cache level        */
  stream = (prfop[0] != 0);            /* streaming (non-temporal)  */
  Hint_Prefetch(address, hint, target, stream);
}}

/** ENUMERATE:aarch64/instrs/system/barriers/barrierop/MemBarrierOp */
/** ENUMERATE:aarch64/instrs/system/hints/syshintop/SystemHintOp */
/** ENUMERATE:aarch64/instrs/system/register/cpsr/pstatefield/PSTATEField */
/** FUNCTION:aarch64/translation/faults/AArch64.AlignmentFault */

function FaultRecord AArch64_AlignmentFault(acctype : AccType, iswrite : boolean, secondstage : boolean) = {
  ipaddress : bits(48) = UNKNOWN;
  level : uinteger = UNKNOWN;
  extflag : bit = UNKNOWN;
  s2fs1walk : boolean = UNKNOWN;

  AArch64_CreateFaultRecord(Fault_Alignment, ipaddress, level, acctype, iswrite,
                            extflag, secondstage, s2fs1walk);
}

/** FUNCTION:aarch64/translation/faults/AArch64.NoFault */

function FaultRecord AArch64_NoFault() = {
  ipaddress : bits(48) = UNKNOWN;
  level : uinteger = UNKNOWN;
  acctype : AccType = AccType_NORMAL;
  iswrite : boolean = UNKNOWN;
  extflag : bit = UNKNOWN;
  secondstage : boolean = false;
  s2fs1walk : boolean = false;

  AArch64_CreateFaultRecord(Fault_None, ipaddress, level, acctype, iswrite,
                            extflag, secondstage, s2fs1walk);
}

/** FUNCTION:aarch64/translation/translation/AArch64.TranslateAddress */

function AArch64_TranslateAddress
           (vaddress : bits(64), acctype : AccType, iswrite : boolean,
           wasaligned : boolean, size : uinteger) -> AddressDescriptor = {
  info("Translation is not implemented, return same address as the virtual (no fault, normal, shareable, non-secure).");
  result : AddressDescriptor = {
    fault = AArch64_NoFault();
    memattrs = {MA_type = MemType_Normal; shareable = true};
    paddress = {physicaladdress = vaddress; NS = 1};
  };
  /* ARM: uncomment when implementing TLB and delete the code above
  (AddressDescriptor) result = AArch64_FullTranslate(vaddress, acctype, iswrite, wasaligned, size);

  if ~(acctype == AccType_PTW | acctype ==  AccType_IC | acctype ==  AccType_AT) & ~(IsFault(result)) then
    result.fault = AArch64_CheckDebug(vaddress, acctype, iswrite, size);
  */

  result;
}

