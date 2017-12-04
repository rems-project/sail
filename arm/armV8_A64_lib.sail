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

(** FUNCTION:aarch64/exceptions/aborts/AArch64.Abort *)

function unit AArch64_Abort((bit[64]) vaddress, (FaultRecord) fault) =
{
  not_implemented("AArch64_Abort");
}

(** FUNCTION:AArch64.SPAlignmentFault() *)

function unit effect pure AArch64_SPAlignmentFault() = {
  not_implemented("AArch64_SPAlignmentFault");
}

(** FUNCTION:aarch64/exceptions/debug/AArch64.SoftwareBreakpoint *)

function unit AArch64_SoftwareBreakpoint((bit[16]) immediate) =
{
  not_implemented("AArch64_SoftwareBreakpoint");
}

(** FUNCTION:aarch64/exceptions/exceptions/AArch64.TakeReset *)

function unit effect {wreg} AArch64_TakeReset((boolean) cold_reset) =
{
  assert((~(HighestELUsingAArch32())), None);

  (* Enter the highest implemented Exception level in AArch64 state *)
  PSTATE_nRW := 0;
  if HaveEL(EL3) then {
    PSTATE_EL := EL3;
    SCR_EL3.NS := 0; (* Secure state *)
  } else if HaveEL(EL2) then
    PSTATE_EL := EL2
  else
    PSTATE_EL := EL1;

  (* Reset the system registers and other system components *)
  AArch64_ResetControlRegisters(cold_reset);

  (* Reset all other PSTATE fields *)
  PSTATE_SP := 0;           (* Select stack pointer               *)
  wPSTATE_DAIF() := 0b1111; (* All asynchronous exceptions masked *)
  PSTATE_SS := 0;           (* Clear software step bit            *)
  PSTATE_IL := 0;           (* Clear illegal execution state bit  *)

  (* All registers, bits and fields not reset by the above pseudocode or by the BranchTo() call *)
  (* below are UNKNOWN bitstrings after reset. In particular, the return information registers  *)
  (* ELR_ELx and SPSR_ELx have UNKNOWN values, so that it is impossible to return from a reset  *)
  (* in an architecturally defined way.                                                         *)
  AArch64_ResetGeneralRegisters();
  AArch64_ResetSIMDFPRegisters();
  AArch64_ResetSpecialRegisters();
  ResetExternalDebugRegisters(cold_reset);

  (bit[64]) rv := 0; (* ARM: uninitialized *) (* IMPLEMENTATION DEFINED reset vector *)
  if HaveEL(EL3) then
    rv := RVBAR_EL3
  else if HaveEL(EL2) then
    rv := RVBAR_EL2
  else
    rv := RVBAR_EL1;

  (* The reset vector must be correctly aligned *)
  assert((IsZero(rv[63..(PAMax())]) & IsZero(rv[1..0])), Some("reset vector not correctly aligned"));

  BranchTo(rv, BranchType_UNKNOWN);
}

(** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallHypervisor *)

function unit AArch64_CallHypervisor((bit[16]) immediate) =
{
  not_implemented("AArch64_CallHypervisor");
}

(** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallSecureMonitor *)

function unit AArch64_CallSecureMonitor((bit[16]) immediate) =
{
  not_implemented("AArch64_CallSecureMonitor");
}

(** FUNCTION:aarch64/exceptions/syscalls/AArch64.CallSupervisor *)

function unit AArch64_CallSupervisor((bit[16]) immediate) =
{
  not_implemented("AArch64_CallSupervisor");
}

(** FUNCTION:aarch64/exceptions/traps/AArch64.CheckForSMCTrap *)

function unit AArch64_CheckForSMCTrap((bit[16]) imm) =
{
  (boolean) route_to_el2 := (HaveEL(EL2) & ~(IsSecure()) & (PSTATE_EL == EL0 | PSTATE_EL == EL1) & HCR_EL2.TSC == 1);
  if route_to_el2 then {
    not_implemented("AArch64_CheckForSMCTrap route_to_el2");
    (* ARM:
    bits(64) preferred_exception_return = ThisInstrAddr();
    vect_offset = 0x0;
    exception = ExceptionSyndrome(Exception_MonitorCall);
    exception.syndrome<15:0> = imm;
    AArch64.TakeException(EL2, exception, preferred_exception_return, vect_offset);
    *)
  };
}

(** FUNCTION:aarch64/exceptions/traps/AArch64.CheckForWFxTrap *)

function unit effect {rreg} AArch64_CheckForWFxTrap((bit[2]) target_el, (boolean) is_wfe) =
{
    assert((HaveEL(target_el)), None);

    (boolean) trap := false; (* ARM: uninitialized *)

    if      target_el == EL1 then trap := ((if is_wfe then SCTLR_EL1.nTWE else SCTLR_EL1.nTWI) == 0)
    else if target_el == EL2 then trap := ((if is_wfe then HCR_EL2.TWE else HCR_EL2.TWI) == 1)
    else if target_el == EL3 then trap := ((if is_wfe then SCR_EL3.TWE else SCR_EL3.TWI) == 1)
    else {assert(false,None); ()};


    if trap then
        AArch64_WFxTrap(target_el, is_wfe);
}

(** FUNCTION:aarch64/exceptions/traps/AArch64.SystemRegisterTrap *)

function unit AArch64_SystemRegisterTrap((bit[2]) target_el, (bit[2]) op0, (bit[3]) op2, (bit[3]) op1, (bit[4]) crn,
                                         (bit[5]) rt, (bit[4]) crm, (bit) dir) =
{
  not_implemented("AArch64_SystemRegisterTrap");
}

(** FUNCTION:aarch64/exceptions/traps/AArch64.UndefinedFault *)

function unit AArch64_UndefinedFault() =
{
  not_implemented("AArch64_UndefinedFault");
}

(** FUNCTION:aarch64/exceptions/traps/AArch64.WFxTrap *)

function unit AArch64_WFxTrap((bit[2]) target_el, (boolean) is_wfe) =
{
  not_implemented("AArch64_WFxTrap");
}

(** FUNCTION:aarch64/functions/aborts/AArch64.CreateFaultRecord *)

function FaultRecord AArch64_CreateFaultRecord((Fault) type, (bit[48]) ipaddress,
                                               (uinteger) level, (AccType) acctype, (boolean) write, (bit) extflag,
                                               (boolean) secondstage, (boolean) s2fs1walk) =
{
  (FaultRecord) fault := {
    type = type;
    domain = (bit[4]) UNKNOWN;
    debugmoe = (bit[4]) UNKNOWN;
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

(** FUNCTION:aarch64/functions/exclusive/AArch64.ExclusiveMonitorsPass *)

function boolean AArch64_ExclusiveMonitorsPass((bit[64]) address, (uinteger) size) =
{
  (*It is IMPLEMENTATION DEFINED whether the detection of memory aborts happens*)
  (*before or after the check on the local Exclusive Monitor. As a result a failure*)
  (*of the local monitor can occur on some implementations even if the memory*)
  (*access would give an memory abort.*)

  (AccType) acctype := AccType_ATOMIC;
  (boolean) iswrite := true;
  (boolean) aligned := (address == Align(address, size));

  if ~(aligned) then {
    (boolean) secondstage := false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
  };

  (boolean) passed := AArch64_IsExclusiveVA(address, ProcessorID(), size);
  if ~(passed) then
    (* return *) false
  else {

  (AddressDescriptor) memaddrdesc := AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);

  (*Check for aborts or debug exceptions*)
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  passed := IsExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);

  if passed then {
      ClearExclusiveLocal(ProcessorID());
      if (memaddrdesc.memattrs).shareable then
          passed := IsExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size);
  };

  passed;
}}

(** FUNCTION:aarch64/functions/exclusive/AArch64.IsExclusiveVA *)

function boolean AArch64_IsExclusiveVA((bit[64]) address, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

(** FUNCTION:aarch64/functions/exclusive/AArch64.MarkExclusiveVA *)

function unit effect pure AArch64_MarkExclusiveVA((bit[64]) address, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

(** FUNCTION:aarch64/functions/exclusive/AArch64.SetExclusiveMonitors *)

function unit AArch64_SetExclusiveMonitors((bit[64]) address, (uinteger) size) =
{
  (AccType) acctype := AccType_ATOMIC;
  (boolean) iswrite := false;
  (boolean) aligned := (address != Align(address, size));

  (AddressDescriptor) memaddrdesc := AArch64_TranslateAddress(address, acctype, iswrite, aligned, size);

  (* Check for aborts or debug exceptions *)
  if IsFault(memaddrdesc) then
    (* return *) ()
  else {

  if (memaddrdesc.memattrs).shareable then
    MarkExclusiveGlobal(memaddrdesc.paddress, ProcessorID(), size);

  MarkExclusiveLocal(memaddrdesc.paddress, ProcessorID(), size);

  AArch64_MarkExclusiveVA(address, ProcessorID(), size);
}}

(** FUNCTION:aarch64/functions/memory/AArch64.CheckAlignment *)

function boolean AArch64_CheckAlignment((bit[64]) address, (uinteger) size, (AccType) acctype, (boolean) iswrite) =
{
  (boolean) aligned := (address == Align(address, size));
  (bit) A := (SCTLR'()).A;

  if ~(aligned) & (acctype == AccType_ATOMIC | acctype == AccType_ORDERED | A == 1) then {
    secondstage := false;
    AArch64_Abort(address, AArch64_AlignmentFault(acctype, iswrite, secondstage));
  };

  aligned;
}

(** FUNCTION:// AArch64.MemSingle[] - non-assignment (read) form *)

function forall Nat 'N, 'N IN {1,2,4,8,16}. (*bit['N*8]*) read_buffer_type effect {rmem} AArch64_rMemSingle((read_buffer_type) read_buffer, (bit[64]) address, ([:'N:]) size, (AccType) acctype, (boolean) wasaligned, (bool) exclusive) =
{
  (*assert size IN {1, 2, 4, 8, 16};*)
  assert((address == Align(address, size)), None);

  (* ARM: AddressDescriptor memaddrdesc; *)
  (bit['N*8]) value := 0;
  (boolean) iswrite := false;

  (* MMU or MPU *)
  (AddressDescriptor) memaddrdesc := AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size);

  (* Check for aborts or debug exceptions *)
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  (* Memory array access *)
  _rMem(read_buffer, memaddrdesc, size, acctype, exclusive);
}

(** FUNCTION:// AArch64.MemSingle[] - assignment (write) form *)

function forall Nat 'N, 'N IN {1,2,4,8,16}. write_buffer_type effect pure AArch64_wMemSingle((write_buffer_type) write_buffer, (bit[64]) address, ([:'N:]) size, (AccType) acctype, (boolean) wasaligned, (bool) exclusive, (bit['N*8]) value) =
{
  (*assert size IN {1, 2, 4, 8, 16};*)
  assert((address == Align(address, size)), None);

  (* ARM: AddressDescriptor memaddrdesc; *)
  (boolean) iswrite := true;

  (* MMU or MPU *)
  (AddressDescriptor) memaddrdesc := AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size);

  (* Check for aborts or debug exceptions *)
  if IsFault(memaddrdesc) then
    AArch64_Abort(address, memaddrdesc.fault);

  (* Effect on exclusives *)
  if (memaddrdesc.memattrs).shareable then
    ClearExclusiveByAddress(memaddrdesc.paddress, ProcessorID(), size);

  (* Memory array access *)
  _wMem(write_buffer, memaddrdesc, size, acctype, exclusive, value)
}

(** FUNCTION:CheckSPAlignment() *)

function unit effect {rreg} CheckSPAlignment() = {
    (bit[64]) sp := rSP();
    (bool) stack_align_check := false; (* ARM: this is missing from ARM ARM *)

    if PSTATE_EL == EL0 then
        stack_align_check := (SCTLR_EL1.SA0 != 0)
    else
        stack_align_check := ((SCTLR'()).SA != 0);

    if stack_align_check & sp != Align(sp, 16) then
        AArch64_SPAlignmentFault();
}

(** FUNCTION://   Mem[] - non-assignment (read) form *)

function forall Nat 'N, 'N IN {1,2,4,8,16}. (*bit['N*8]*) read_buffer_type effect {rmem} rMem'((read_buffer_type) read_buffer, (bit[64]) address,([:'N:]) size, (AccType) acctype, (bool) exclusive) =
{
  (* ARM: assert size IN {1, 2, 4, 8, 16}; *)
  (read_buffer_type) read_buffer' := read_buffer;

  (uinteger) i := 0; (* ARM: uninitialized *)
  (boolean) iswrite := false;

  (boolean) aligned := AArch64_CheckAlignment(address, size, acctype, iswrite);
  (boolean) atomic := ((aligned & ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM)) | size == 1);

  if ~(atomic) then {
    assert((~(exclusive)), None); (* as far as I can tell this should never happen *)

    assert((size > 1), None);
    if (~(exclusive)) then {
     (*value[7..0] :=*)read_buffer' :=  AArch64_rMemSingle(read_buffer', address, 1, acctype, aligned, false);

    (* For subsequent bytes it is CONSTRAINED UNPREDICTABLE whether an unaligned Device memory *)
    (* access will generate an Alignment Fault, as to get this far means the first byte did    *)
    (* not, so we must be changing to a new translation page.                                  *)
    (* FIXME: ???
    if ~(aligned) then {
      c = ConstrainUnpredictable();
      assert c IN {Constraint_FAULT, Constraint_NONE};
      if c == Constraint_NONE then aligned = TRUE;
    };*)

    foreach (i from 1 to (size - 1)) {
      (*value[(8*i+7)..(8*i)] :=*)read_buffer' := AArch64_rMemSingle(read_buffer', address+i, 1, acctype, aligned, false);
  }}} else 
    (*value :=*)read_buffer' := AArch64_rMemSingle(read_buffer', address, size, acctype, aligned, exclusive);

  (*if BigEndian() then
    value := BigEndianReverse(value);
  value;*)
  read_buffer'
}

function forall Nat 'N, 'N IN {1,2,4,8,16}. (*bit['N*8]*) read_buffer_type effect {rmem} rMem((read_buffer_type) read_buffer, (bit[64]) address,([:'N:]) size, (AccType) acctype) =
  rMem'(read_buffer, address, size, acctype, false)

function forall Nat 'N, 'N IN {1,2,4,8,16}. (*bit['N*8]*) read_buffer_type effect {rmem} rMem_exclusive((read_buffer_type) read_buffer, (bit[64]) address,([:'N:]) size, (AccType) acctype) =
  rMem'(read_buffer, address, size, acctype, true)

(** FUNCTION:// Mem[] - assignment (write) form *)

(* the 'exclusive' and return value are our addition for handling
   store-exclusive, this function should only be called indirectly by one
   of the functions that follow it.
   returns true if the store-exclusive was successful. *)
function forall Nat 'N, 'N IN {1,2,4,8,16}. write_buffer_type wMem'((write_buffer_type) write_buffer, (bit[64]) address, ([:'N:]) size, (AccType) acctype, (bit['N*8]) value, (bool) exclusive) =
{
  (write_buffer_type) write_buffer' := write_buffer;

  (* sail doesn't allow assignment to function arguments *)
  (bit['N*8]) value' := value;

  (uinteger) i := 0; (* ARM: uninitialized *)
  (boolean) iswrite := true;

  if BigEndian() then
    value' := BigEndianReverse(value');
  (boolean) aligned := AArch64_CheckAlignment(address, size, acctype, iswrite);
  (boolean) atomic := ((aligned & ~(acctype == AccType_VEC | acctype == AccType_VECSTREAM)) | size == 1);

  (bool) exclusiveSuccess := false;
  if ~(atomic) then {
    assert((~(exclusive)), None); (* as far as I can tell this should never happen *)

    if (~(exclusive)) then {
    assert((size > 1), None);
    write_buffer' := AArch64_wMemSingle(write_buffer', address, 1, acctype, aligned, false, value'[7..0]);

    (* For subsequent bytes it is CONSTRAINED UNPREDICTABLE whether an unaligned Device memory *)
    (* access will generate an Alignment Fault, as to get this far means the first byte did    *)
    (* not, so we must be changing to a new translation page.                                  *)
    (* FIXME:
    if !aligned then
      c = ConstrainUnpredictable();
      assert c IN {Constraint_FAULT, Constraint_NONE};
      if c == Constraint_NONE then aligned = TRUE;*)

    foreach (i from 1 to (size - 1))
      write_buffer' := AArch64_wMemSingle(write_buffer', address+i, 1, acctype, aligned, false, value'[(8*i+7)..(8*i)]);
  }} else
      write_buffer' := AArch64_wMemSingle(write_buffer', address, size, acctype, aligned, exclusive, value');

  write_buffer'
}

function forall Nat 'N, 'N IN {1,2,4,8,16}. write_buffer_type wMem((write_buffer_type) write_buffer, (bit[64]) address, ([:'N:]) size, (AccType) acctype, (bit['N*8]) value) =
  wMem'(write_buffer, address, size, acctype, value, false)

function forall Nat 'N, 'N IN {1,2,4,8,16}. write_buffer_type wMem_exclusive((write_buffer_type) write_buffer, (bit[64]) address, ([:'N:]) size, (AccType) acctype, (bit['N*8]) value) =
  wMem'(write_buffer, address, size, acctype, value, true)

(** FUNCTION:aarch64/functions/registers/AArch64.ResetGeneralRegisters *)

function unit AArch64_ResetGeneralRegisters() =
{
  foreach (i from 0 to 30)
    wX(i) := (bit[64]) UNKNOWN;
}

(** FUNCTION:aarch64/functions/registers/AArch64.ResetSIMDFPRegisters *)

function unit AArch64_ResetSIMDFPRegisters() =
{
  foreach (i from 0 to 31)
    wV(i) := (bit[128]) UNKNOWN;
}

(** FUNCTION:aarch64/functions/registers/AArch64.ResetSpecialRegisters *)

function unit AArch64_ResetSpecialRegisters() =
{
  (* AArch64 special registers *)
  SP_EL0 := (bit[64]) UNKNOWN;
  SP_EL1 := (bit[64]) UNKNOWN;
  SPSR_EL1 := (bit[32]) UNKNOWN;
  ELR_EL1 := (bit[64]) UNKNOWN;
  if HaveEL(EL2) then {
    SP_EL2 := (bit[64]) UNKNOWN;
    SPSR_EL2 := (bit[32]) UNKNOWN;
    ELR_EL2 := (bit[64]) UNKNOWN;
  };
  if HaveEL(EL3) then {
    SP_EL3 := (bit[64]) UNKNOWN;
    SPSR_EL3 := (bit[32]) UNKNOWN;
    ELR_EL3 := (bit[64]) UNKNOWN;
  };

  (* AArch32 special registers that are not architecturally mapped to AArch64 registers *)
  if HaveAArch32EL(EL1) then {
    SPSR_fiq := (bit[32]) UNKNOWN;
    SPSR_irq := (bit[32]) UNKNOWN;
    SPSR_abt := (bit[32]) UNKNOWN;
    SPSR_und := (bit[32]) UNKNOWN;
  };

  (* External debug special registers *)
  DLR_EL0 := (bit[64]) UNKNOWN;
  DSPSR_EL0 := (bit[32]) UNKNOWN;
}

(** FUNCTION:aarch64/functions/registers/PC *)

function bit[64] effect {rreg} rPC () = _PC

(** FUNCTION:// SP[] - assignment form *)

function forall Nat 'N, 'N IN {32,64}. unit effect {rreg,wreg} wSP ((),(bit['N]) value) =
{
  (*assert width IN {32,64};*)
  if PSTATE_SP == 0 then
    SP_EL0 := ZeroExtend(value)
  else
    let pstate_el = PSTATE_EL in {
      if      pstate_el == EL0 then SP_EL0 := ZeroExtend(value)
      else if pstate_el == EL1 then SP_EL1 := ZeroExtend(value)
      else if pstate_el == EL2 then SP_EL2 := ZeroExtend(value)
      else if pstate_el == EL3 then SP_EL3 := ZeroExtend(value)
      else assert(false,None); ();
    }
}

(** FUNCTION:// SP[] - non-assignment form *)

function bit['N] effect {rreg} rSP () =
{
  (*assert width IN {8,16,32,64};*)
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

(** FUNCTION://   V[] - assignment form *)

function forall Nat 'N, 'N IN {8,16,32,64,128}. unit effect {wreg} wV((SIMD_index) n, (bit['N]) value) = {
  (*assert n >= 0 && n <= 31;*)
  (*assert width IN {8,16,32,64,128};*)
  _V[n] := ZeroExtend(value);
}

(** FUNCTION://   V[] - non-assignment form *)

function forall Nat 'N, 'N IN {8,16,32,64,128}. bit['N] effect {rreg} rV((SIMD_index) n) = mask(_V[n])


(** FUNCTION:// Vpart[] - non-assignment form *)

function forall Nat 'N, 'N IN {8,16,32,64,128}. bit['N] effect {rreg} rVpart (n,part) = {
  if part == 0 then
    ((bit['N]) (mask(_V[n])))
  else {
    assert((length((bit['N]) 0) == 64), None);
    ((bit[64]) ((_V[n])[127..64]));
  }
}

(** FUNCTION:// Vpart[] - assignment form *)

function forall Nat 'N, 'N IN {8,16,32,64,128}. unit effect {wreg} wVpart((SIMD_index) n, ([|1|]) part, (bit['N]) value) = {
  if part == 0 then
    _V[n] := ZeroExtend(value)
  else {
    assert((length((bit['N]) 0) == 64), None);
    (_V[n])[127..64] := value;
  }
}

(** FUNCTION:// X[] - assignment form *)

function forall Nat 'N, 'N IN {32,64}. unit effect {wreg} wX((reg_index) n, (bit['N]) value) =
{
  (*assert n >= 0 && n <= 31;*)
  (*assert width IN {32,64};*)
  if n != 31 then
    _R[n] := ZeroExtend(value);
}

(** FUNCTION:// X[] - non-assignment form *)

function forall Nat 'N, 'N IN {8,16,32,64}. bit['N] effect {rreg} rX((reg_index) n) =
{
  (*assert n >= 0 && n <= 31;*)
  (*assert width IN {8,16,32,64};*)
  if n != 31 then
    mask(_R[n])
  else
    Zeros();
}

(** FUNCTION:bits(64) ELR[bits(2) el] *)

function bit[64] rELR((bit[2]) el) =
{
  (bit[64]) r := 0; (* ARM: uninitialized *)
  if      el == EL1 then r := ELR_EL1
  else if el == EL2 then r := ELR_EL2
  else if el == EL3 then r := ELR_EL3
  else Unreachable();
  r;
}

(** FUNCTION:bits(64) ELR[] *)

function bit[64] rELR'() =
{
    assert (PSTATE_EL != EL0, None);
    rELR(PSTATE_EL);
}

(** FUNCTION:SCTLRType SCTLR[bits(2) regime] *)

function SCTLR_type effect {rreg} SCTLR ((bit[2]) regime) = {
   if      regime == EL1 then SCTLR_EL1
   else if regime == EL2 then SCTLR_EL2
   else if regime == EL3 then SCTLR_EL3
   else {assert(false,Some("SCTLR_type unreachable")); SCTLR_EL1} (* ARM: Unreachabe() *)
}

(** FUNCTION:SCTLRType SCTLR[] *)

function SCTLR_type effect {rreg} SCTLR' () = SCTLR(S1TranslationRegime())

(** FUNCTION:aarch64/functions/system/AArch64.CheckUnallocatedSystemAccess *)

(* return true if the access is not allowed *)
function boolean AArch64_CheckUnallocatedSystemAccess ((bit[2]) op0, (bit[3]) op1, (bit[4]) crn, (bit[4]) crm, (bit[3]) op2, (bit) read) =
{
  switch (op0,op1,crn,crm,op2, read) {
    case (0b00,0b000,0b0100,_,0b101, _) -> PSTATE_EL < EL1 (* SPSel *)
    case (0b00,0b011,0b0100,_,0b110, _) -> false (* DAIFSet *) (* TODO: EL0 Config-RW ??? *)
    case (0b00,0b011,0b0100,_,0b111, _) -> false (* DAIFClr *) (* TODO: EL0 Config-RW ??? *)

    (* follow the "Usage constraints" of each register *)
    case (0b11,0b011,0b0100,0b0010,0b000, _) -> false (* NZCV *)
    case (0b11,0b011,0b0100,0b0010,0b001, _) -> false (* DAIF *) (* TODO: EL0 Config-RW ??? *)
(*     case (0b11,0b000,0b0001,0b0000,0b001, _) -> PSTATE_EL < EL1 (* ACTLR_EL1 *) *)
  }
}

(** FUNCTION:aarch64/functions/system/CheckSystemAccess *)

function unit CheckSystemAccess((bit[2]) op0, (bit[3]) op1, (bit[4]) crn, (bit[4]) crm, (bit[3]) op2, (bit[5]) rt, (bit) read) =
{
  (*Checks if an AArch64 MSR/MRS/SYS instruction is UNALLOCATED or trapped at the current exception*)
  (*level, security state and configuration, based on the opcode's encoding.*)
  (boolean) unallocated := false;
  (boolean) need_secure := false;
  (bit[2]) min_EL := 0; (* ARM: uninitialized *)

  (*Check for traps by HCR_EL2.TIDCP*)
  (* TODO: uncomment when implementing traps
  if HaveEL(EL2) & ~(IsSecure()) & HCR_EL2.TIDCP == 1 & op0[0] == 1 & (switch crn {case [1,_,1,1] -> true case _ -> false}) then {
    (*At Non-secure EL0, it is IMPLEMENTATION_DEFINED whether attempts to execute system control*)
    (*register access instructions with reserved encodings are trapped to EL2 or UNDEFINED*)
    if PSTATE_EL == EL0 (* FIXME: & boolean IMPLEMENTATION_DEFINED "Reserved Control Space EL0 Trapped" *) then
      AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read)
    else if PSTATE.EL == EL1 then
      AArch64_SystemRegisterTrap(EL2, op0, op2, op1, crn, rt, crm, read);
  };*)

  (*Check for unallocated encodings*)
  switch op1 {
    case (0b00:[_]) ->
      min_EL := EL1
    case 0b010 ->
      min_EL := EL1
    case 0b011 ->
      min_EL := EL0
    case 0b100 ->
      min_EL := EL2
    case 0b101 ->
      UnallocatedEncoding()
    case 0b110 ->
      min_EL := EL3
    case 0b111 -> {
      min_EL := EL1;
      need_secure := true;
    }
  };
  if PSTATE_EL < min_EL then (* ARM: UInt *)
      UnallocatedEncoding()
  else if need_secure & ~(IsSecure()) then
      UnallocatedEncoding()
  else if AArch64_CheckUnallocatedSystemAccess(op0, op1, crn, crm, op2, read) then
      UnallocatedEncoding();
  (*Check for traps on accesses to SIMD or floating-point registers*)
  (* TODO: uncomment when implementing SIMD/FP
  let (take_trap, target_el) = AArch64.CheckAdvSIMDFPSystemRegisterTraps(op0, op1, crn, crm, op2) in {
    if take_trap then
      AArch64_AdvSIMDFPAccessTrap(target_el);
  };*)

  (*Check for traps on access to all other system registers*)
  (* TODO: uncomment when implementing traps
  let (take_trap, target_el) = AArch64_CheckSystemRegisterTraps(op0, op1, crn, crm, op2, read) in {
    if take_trap then
        AArch64_SystemRegisterTrap(target_el, op0, op2, op1, crn, rt, crm, read);
  };*)
}

(** FUNCTION:aarch64/functions/system/SysOp_R *)

function bit[64] SysOp_R((uinteger) op0, (uinteger) op1, (uinteger) crn, (uinteger) crm, (uinteger) op2) =
{
  not_implemented("SysOp_R");
  0;
}

(** FUNCTION:aarch64/functions/system/SysOp_W *)

function unit SysOp_W((uinteger) op0, (uinteger) op1, (uinteger) crn, (uinteger) crm, (uinteger) op2, (bit[64]) _val) =
{
  not_implemented("SysOp_W");
}

(** FUNCTION:bits(64) System_Get(integer op0, integer op1, integer crn, integer crm, integer op2); *)

function bit[64] System_Get((uinteger) op0, (uinteger) op1, (uinteger) crn, (uinteger) crm, (uinteger) op2) = {
  switch (op0,op1,crn,crm,op2) {
    case (3,3,4,2,0) -> ZeroExtend(NZCV)
    case (3,3,4,2,1) -> ZeroExtend(DAIF)
    case (3, 3, 13, 0, 2) -> TPIDR_EL0
  (* TODO FIXME: higher EL TPIDRs *)

(*     case (3,0,1,0,1) -> ZeroExtend(ACTLR_EL1) *)
  }
}

(** FUNCTION:System_Put(integer op0, integer op1, integer crn, integer crm, integer op2, bits(64) val); *)

function unit effect {wreg} System_Put((uinteger) op0, (uinteger) op1, (uinteger) crn, (uinteger) crm, (uinteger) op2, (bit[64]) _val) = {
  switch (op0,op1,crn,crm,op2) {
    case (3,3,4,2,0) -> NZCV := _val[31..0]
    case (3,3,4,2,1) -> DAIF := _val[31..0]
    case (3, 3, 13, 0, 2) -> TPIDR_EL0 := _val[63..0]
  (* TODO FIXME: higher EL TPIDRs *)

(*     case (3,0,1,0,1) -> ACTLR_EL1 := _val[31..0] *)
  }
}

(** FUNCTION:aarch64/instrs/branch/eret/AArch64.ExceptionReturn *)

function unit AArch64_ExceptionReturn((bit[64]) new_pc, (bit[32]) spsr) =
{
  not_implemented("AArch64_ExceptionReturn");
}

(** ENUMERATE:aarch64/instrs/countop/CountOp *)
(** FUNCTION:ExtendType DecodeRegExtend(bits(3) op) *)

function ExtendType DecodeRegExtend ((bit[3]) op) =
{
  switch op {
    case 0b000 -> ExtendType_UXTB
    case 0b001 -> ExtendType_UXTH
    case 0b010 -> ExtendType_UXTW
    case 0b011 -> ExtendType_UXTX
    case 0b100 -> ExtendType_SXTB
    case 0b101 -> ExtendType_SXTH
    case 0b110 -> ExtendType_SXTW
    case 0b111 -> ExtendType_SXTX
  }
}

(** FUNCTION:aarch64/instrs/extendreg/ExtendReg *)

val forall Nat 'N, Nat 'S, 'N IN {8,16,32,64}, 'S >= 0, 'S <= 4.
    (implicit<'N>,reg_index,ExtendType,[:'S:]) -> bit['N] effect {rreg} ExtendReg
function bit['N] ExtendReg ((reg_index) _reg, (ExtendType) type, ([:'S:]) shift) =
{
  (*assert( shift >= 0 & shift <= 4 );*)
  (bit['N]) _val := rX(_reg);
  (boolean) _unsigned := false;
  (uinteger) len := 0;

  switch type {
    case ExtendType_SXTB -> { _unsigned := false; len := 8}
    case ExtendType_SXTH -> { _unsigned := false; len := 16}
    case ExtendType_SXTW -> { _unsigned := false; len := 32}
    case ExtendType_SXTX -> { _unsigned := false; len := 64}
    case ExtendType_UXTB -> { _unsigned := true; len := 8}
    case ExtendType_UXTH -> { _unsigned := true; len := 16}
    case ExtendType_UXTW -> { _unsigned := true; len := 32}
    case ExtendType_UXTX -> { _unsigned := true; len := 64}
  };

  len := uMin(len, length(_val) - shift);
  Extend((_val[(len - 1)..0]) : ((bit['S]) (Zeros())), _unsigned)
}

(** ENUMERATE:aarch64/instrs/extendreg/ExtendType *)
(** ENUMERATE:aarch64/instrs/integer/arithmetic/rev/revop/RevOp *)
(** FUNCTION:(bits(M), bits(M)) DecodeBitMasks (bit immN, bits(6) imms, bits(6) immr, boolean immediate) *)

val forall Nat 'M, Nat 'E. (implicit<'M>,bit,bit[6],bit[6],boolean) -> (bit['M],bit['M]) effect {escape} DecodeBitMasks
function forall Nat 'M, Nat 'E, 'E IN {2,4,8,16,32,64}. (bit['M],bit['M]) DecodeBitMasks((bit) immN, (bit[6]) imms, (bit[6]) immr, (boolean) immediate) = {
  let M = (length((bit['M]) 0)) in {
(* ARM: (bit['M]) tmask := 0; (* ARM: uninitialized *) *)
(* ARM: (bit['M]) wmask := 0; (* ARM: uninitialized *) *)
  (bit[6]) levels := 0; (* ARM: uninitialized *)

  (* Compute log2 of element size *)
  (* 2^len must be in range [2, 'M] *)
  ([|6|]) len := switch HighestSetBit([immN]:(NOT(imms))) {
    case None -> { assert (false,Some("DecodeBitMasks: HighestSetBit returned None")); 0; }
    case (Some(c)) -> c
  };
  if len < 1 then ReservedValue();
  assert((M >= lsl(1, len)),None);

  (* Determine S, R and S - R parameters *)
  levels := ZeroExtend(0b1 ^^ len);

  (* For logical immediates an all-ones value of S is reserved *)
  (* since it would generate a useless all-ones result (many times) *)
  if immediate & ((imms & levels) == levels) then
    ReservedValue();

  (bit[6]) S := (imms & levels);
  (bit[6]) R := (immr & levels);
  (bit[6]) diff := S - R; (* 6-bit subtract with borrow *)

  ([:'E:]) esize := lsl(1, len);
  (bit[6]) d := diff[(len - 1)..0];
  (bit['E]) welem := ZeroExtend(0b1 ^^ (S + 1));
  (bit['E]) telem := ZeroExtend(0b1 ^^ (d + 1));
  wmask := Replicate(ROR(welem, R));
  tmask := Replicate(telem);
  (wmask, tmask);
}}

(** ENUMERATE:aarch64/instrs/integer/ins-ext/insert/movewide/movewideop/MoveWideOp *)
(** FUNCTION:ShiftType DecodeShift(bits(2) op) *)

function ShiftType DecodeShift((bit[2]) op) = ([|4|]) op

(** FUNCTION:bits(N) ShiftReg(integer reg, ShiftType type, integer amount) *)

val forall Nat 'N. (implicit<'N>,reg_index,ShiftType,nat) -> bit['N] effect {rreg} ShiftReg
function forall Nat 'N. bit['N] effect {rreg} ShiftReg((reg_index) _reg, (ShiftType) type, (nat) amount) = {
  (bit['N]) result := rX(_reg);
  switch type {
    case ShiftType_LSL -> result := LSL(result, amount)
    case ShiftType_LSR -> result := LSR(result, amount)
    case ShiftType_ASR -> result := ASR(result, amount)
    case ShiftType_ROR -> result := ROR(result, amount)
  };
  result;
}

(** ENUMERATE:aarch64/instrs/integer/shiftreg/ShiftType *)
(** ENUMERATE:aarch64/instrs/logicalop/LogicalOp *)
(** ENUMERATE:aarch64/instrs/memory/memop/MemOp *)
(** FUNCTION:aarch64/instrs/memory/prefetch/Prefetch *)

function unit Prefetch((bit[64]) address, (bit[5]) prfop) =
{
  (PrefetchHint) hint := 0;
  (uinteger) target := 0;
  (boolean) stream := 0;

  (bool) returnv := false;
  switch prfop[4..3] {
    case 0b00 -> hint := Prefetch_READ  (* PLD: prefetch for load    *)
    case 0b01 -> hint := Prefetch_EXEC  (* PLI: preload instructions *)
    case 0b10 -> hint := Prefetch_WRITE (* PST: prepare for store    *)
    case 0b11 -> returnv := true         (* unallocated hint          *)
  };
  if ~(returnv) then {
  target := prfop[2..1];                (* target cache level        *)
  stream := (prfop[0] != 0);            (* streaming (non-temporal)  *)
  Hint_Prefetch(address, hint, target, stream);
}}

(** ENUMERATE:aarch64/instrs/system/barriers/barrierop/MemBarrierOp *)
(** ENUMERATE:aarch64/instrs/system/hints/syshintop/SystemHintOp *)
(** ENUMERATE:aarch64/instrs/system/register/cpsr/pstatefield/PSTATEField *)
(** FUNCTION:aarch64/translation/faults/AArch64.AlignmentFault *)

function FaultRecord AArch64_AlignmentFault((AccType) acctype, (boolean) iswrite, (boolean) secondstage) =
{
  (bit[48]) ipaddress := (bit[48]) UNKNOWN;
  (uinteger) level := (uinteger) UNKNOWN;
  (bit) extflag := (bit) UNKNOWN;
  (boolean) s2fs1walk := (boolean) UNKNOWN;

  AArch64_CreateFaultRecord(Fault_Alignment, ipaddress, level, acctype, iswrite,
                            extflag, secondstage, s2fs1walk);
}

(** FUNCTION:aarch64/translation/faults/AArch64.NoFault *)

function FaultRecord AArch64_NoFault() =
{
     (bit[48]) ipaddress := (bit[48]) UNKNOWN;
     (uinteger) level := (uinteger) UNKNOWN;
     (AccType) acctype := AccType_NORMAL;
     (boolean) iswrite := (boolean) UNKNOWN;
     (bit) extflag := (bit) UNKNOWN;
     (boolean) secondstage := false;
     (boolean) s2fs1walk := false;

     AArch64_CreateFaultRecord(Fault_None, ipaddress, level, acctype, iswrite,
                               extflag, secondstage, s2fs1walk);
}

(** FUNCTION:aarch64/translation/translation/AArch64.TranslateAddress *)

function AddressDescriptor AArch64_TranslateAddress((bit[64]) vaddress, (AccType) acctype, (boolean) iswrite,
                                           (boolean) wasaligned, (uinteger) size) =
{
  info("Translation is not implemented, return same address as the virtual (no fault, normal, shareable, non-secure).");
  (AddressDescriptor) result := {
    fault = AArch64_NoFault();
    memattrs = {type = MemType_Normal; shareable = true};
    paddress = {physicaladdress = vaddress; NS = 1};
  };
  (* ARM: uncomment when implementing TLB and delete the code above
  (AddressDescriptor) result := AArch64_FullTranslate(vaddress, acctype, iswrite, wasaligned, size);

  if ~(acctype == AccType_PTW | acctype ==  AccType_IC | acctype ==  AccType_AT) & ~(IsFault(result)) then
    result.fault := AArch64_CheckDebug(vaddress, acctype, iswrite, size);
  *)

  result;
}

