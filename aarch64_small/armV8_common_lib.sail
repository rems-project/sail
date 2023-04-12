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


/** FUNCTION:shared/functions/system/Unreachable */

/* CP: adding two variants, one that takes a string argument, the other one doesn't  */
val Unreachable_no_message : forall ('a : Type) . unit -> 'a effect{escape}
function Unreachable_no_message() = 
    error("Unreachable reached")

val Unreachable_message : forall ('a : Type) . string -> 'a effect{escape}
function Unreachable_message(message) = 
    error(message)

overload Unreachable = {Unreachable_no_message, Unreachable_message}

/** FUNCTION:shared/debug/DoubleLockStatus/DoubleLockStatus */

function DoubleLockStatus() -> boolean= {
  if ELUsingAArch32(EL1) then
    (DBGOSDLR.DLK() == 0b1 & DBGPRCR.CORENPDRQ() == 0b0 & ~(Halted()))
  else
    (OSDLR_EL1.DLK() == 0b1 & DBGPRCR_EL1.CORENPDRQ() == 0b0 & ~(Halted()));
}

/** FUNCTION:shared/debug/authentication/Debug_authentication */

/* TODO: these are external signals */

enum signalValue = {LOw, HIGH}

function signalDBGEN () -> signalValue = not_implemented_extern("signalDBGEN")
function signelNIDEN () -> signalValue = not_implemented_extern("signalNIDEN")
function signalSPIDEN () -> signalValue = not_implemented_extern("signalSPIDEN")
function signalDPNIDEN () -> signalValue = not_implemented_extern("signalSPNIDEN")

/** FUNCTION:shared/debug/authentication/ExternalInvasiveDebugEnabled */

function ExternalInvasiveDebugEnabled() -> boolean = {
  /* In the recommended interface, ExternalInvasiveDebugEnabled returns the state of the DBGEN */
  /* signal. */
  signalDBGEN() == HIGH;
}

/** FUNCTION:shared/debug/authentication/ExternalSecureInvasiveDebugEnabled */

function ExternalSecureInvasiveDebugEnabled() -> boolean = {
  /* In the recommended interface, ExternalSecureInvasiveDebugEnabled returns the state of the */
  /* (DBGEN AND SPIDEN) signal. */
  /* CoreSight allows asserting SPIDEN without also asserting DBGEN, but this is not recommended. */
  if ~(HaveEL(EL3)) & ~(IsSecure()) then false
  else {
  (ExternalInvasiveDebugEnabled() & signalSPIDEN() == HIGH);
}}

/** FUNCTION:shared/debug/halting/DCPSInstruction */

function DCPSInstruction(target_el : bits(2)) -> unit = {
  not_implemented("DCPSInstruction");
}

/** FUNCTION:shared/debug/halting/DRPSInstruction */

function DRPSInstruction() -> unit = {
  not_implemented("DRPSInstruction");
}

/** TYPE:shared/debug/halting/DebugHalt */

let DebugHalt_Breakpoint        =   0b000111
let DebugHalt_EDBGRQ            =   0b010011
let DebugHalt_Step_Normal       =   0b011011
let DebugHalt_Step_Exclusive    =   0b011111
let DebugHalt_OSUnlockCatch     =   0b100011
let DebugHalt_ResetCatch        =   0b100111
let DebugHalt_Watchpoint        =   0b101011
let DebugHalt_HaltInstruction   =   0b101111
let DebugHalt_SoftwareAccess    =   0b110011
let DebugHalt_ExceptionCatch    =   0b110111
let DebugHalt_Step_NoSyndrome   =   0b111011

/** FUNCTION:shared/debug/halting/Halt */

function Halt(reason : bits(6)) -> unit= {
  not_implemented("Halt");
}

/** FUNCTION:shared/debug/halting/Halted */

function Halted() -> boolean = {
  ~(EDSCR.STATUS() == 0b000001 | EDSCR.STATUS() == 0b000010); /* Halted */
}

/** FUNCTION:shared/debug/halting/HaltingAllowed */

function HaltingAllowed() -> boolean = {
  if Halted() | DoubleLockStatus() then
    false
  else if IsSecure() then
    ExternalSecureInvasiveDebugEnabled()
  else
    ExternalInvasiveDebugEnabled();
}

/** FUNCTION:shared/exceptions/traps/ReservedValue */

function ReservedValue() -> unit = {
  /* ARM: uncomment when adding aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException()
  else*/
    AArch64_UndefinedFault();
}

/** FUNCTION:shared/exceptions/traps/UnallocatedEncoding */

function UnallocatedEncoding() -> unit = {
  /* If the unallocated encoding is an AArch32 CP10 or CP11 instruction, FPEXC.DEX must be written */
  /* to zero. This is omitted from this code. */
  /* ARM: uncomment when implementing aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException();
  else*/
    AArch64_UndefinedFault();
}

/** FUNCTION:shared/functions/aborts/IsFault */

function IsFault(addrdesc : AddressDescriptor) ->  boolean= {
    (addrdesc.fault).faulttype != Fault_None;
}

/** FUNCTION:shared/functions/common/ASR */

/* original: */

/* val ASR : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N) */
/* function ASR (x, shift) =  */
/* { */
/*   /\*assert shift >= 0;*\/ */
/*   result : bits('N) = 0; */
/*   if shift == 0 then */
/*     result = x */
/*   else */
/*     let (result', _) = ASR_C (x, shift) in { result = result' }; */
/*   result; */
/* } */

/* CP: replacing this with the slightly simpler one below */

val ASR : forall 'N, 'N >= 1. (bits('N), uinteger) -> bits('N) effect {escape}
function ASR (x, shift) = {
  /*assert shift >= 0;*/
  if shift == 0 then x
  else let (result', _) = ASR_C (x, shift) in result'
}


/** FUNCTION:shared/functions/common/ASR_C */

function ASR_C (x, shift) =  {
  /*assert shift > 0;*/
  extended_x : bits('S+'N) = SignExtend(x);
  result : bits('N) = extended_x[(shift + length(x) - 1)..shift];
  carry_out : bit = extended_x[shift - 1];
  (result, carry_out);
}

/* SignExtend : */

/* 'S+'N > 'N & 'N >= 1. (int('S+'N),bits('N)) -> bits('S+'N) */


/** FUNCTION:integer Align(integer x, integer y) */

function Align'(x : uinteger, y : uinteger) -> uinteger =
    y * (quot (x,y))

/** FUNCTION:bits(N) Align(bits(N) x, integer y) */

val Align : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N) effect {escape}
function Align (x, y) =
    to_bits (Align'(UInt(x), y))

/** FUNCTION:integer CountLeadingSignBits(bits(N) x) */

val CountLeadingSignBits : forall 'N, 'N >= 2. bits('N) -> range(0,'N - 1)
function CountLeadingSignBits(x) =
  CountLeadingZeroBits( (x[(length(x) - 1)..1]) ^ 
                        (x[(length(x) - 2)..0]) )

/** FUNCTION:integer CountLeadingZeroBits(bits(N) x) */

function CountLeadingZeroBits(x) =
  match HighestSetBit(x) {
    None()  => length(x),
    Some(n)  => length(x) - 1 - n
  }
/** FUNCTION:bits(N) Extend(bits(M) x, integer N, boolean unsigned) */

val Extend : forall 'N 'M, 1 <= 'M & 'M < 'N. (implicit('N),bits('M),bit) -> bits('N) effect {escape}
function Extend (n, x, _unsigned) =
  if _unsigned then ZeroExtend(n,x) else SignExtend(n,x)

/** FUNCTION:integer HighestSetBit(bits(N) x) */

/* val HighestSetBit : forall 'N, 'N >= 0. bits('N) -> option(range(0, 'N - 1)) */
/* function HighestSetBit(x) = { */
/*   let N = (length(x)) in { */
/*   result : range(0,'N - 1) = 0; */
/*   break : bool = false; */
/*   foreach (i from (N - 1) downto 0) */
/*     if ~(break) & (x[i] == b1) then { */
/*       result = i; */
/*       break = true; */
/*     }; */

/*   if break then Some(result) else None; */
/* }} */

function HighestSetBit(x) = {
  let N = length(x) in {
  foreach (i from (N - 1) downto 0)
    if x[i] == b1 then {
      return (Some(i));
    };
  None();
}}


/** FUNCTION:integer Int(bits(N) x, boolean unsigned) */
/* used to be called Int */
val _Int : forall 'N, 'N >= 1. (bits('N), boolean) -> integer effect {escape}
function _Int (x, _unsigned) = {
  if _unsigned then UInt(x) else SInt(x)
}

/** FUNCTION:boolean IsZero(bits(N) x) */

/* function IsZero(x) = x == 0 /\* ARM: Zeros(N) *\/ */
function IsZero(x) = x == Zeros() /* ARM: Zeros(N) */

/** FUNCTION:bit IsZeroBit(bits(N) x) */

val IsZeroBit : forall 'N, 'N >= 0. bits('N) -> bit
function IsZeroBit(x) = if IsZero(x) then b1 else b0

/** FUNCTION:shared/functions/common/LSL */

val LSL : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function LSL(x, shift) =
{
  /*assert shift >= 0;*/
  result : bits('N) = Zeros();
  if shift == 0 then
    result = x
  else
    let (result',_) = LSL_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/LSL_C */

function LSL_C (x, shift) =
{
  /*assert shift > 0;*/
  extended_x : bits('N + 'S) = x @ ((Zeros()) : (bits('S)));
  result : bits('N) = mask(extended_x);
  carry_out : bit = extended_x[length(x)];
  (result, carry_out);
}

/** FUNCTION:shared/functions/common/LSR */

val LSR : forall 'N, 'N >= 1. (bits('N), uinteger) -> bits('N)
function LSR(x, shift) =
{
  /*assert shift >= 0;*/
  result : bits('N) = Zeros();
  if shift == 0 then
    result = x
  else
    let (result', _) = LSR_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/LSR_C */

function LSR_C(x, shift) = {
  /*assert shift > 0;*/
  extended_x : bits('N + 'S) = ZeroExtend(x);
  result : bits('N) = extended_x[(length(x) + shift - 1)..shift];
  carry_out : bit = extended_x[shift - 1];
  (result, carry_out);
}

/** FUNCTION:integer Min(integer a, integer b) */

val Min : forall 'M 'N.(int('M), int('N)) -> min('M,'N)
function Min (a,b) =
  if a <= b then a else b

val uMin : forall 'M 'N, 'M >= 0 & 'N >= 0. (int('M), int('N)) -> min('M,'N)
function uMin (a,b) =
  if a <= b then a else b

/** FUNCTION:bits(N) NOT(bits(N) x); */

val NOT : forall 'N, 'N >= 0. bits('N) -> bits('N)
function NOT(x) = ~(x)

val NOT' : bit -> bit
function NOT'(x) = ~(x)

/** FUNCTION:shared/functions/common/Ones */

function Ones(n) = Replicate(n,[b1])

/** FUNCTION:shared/functions/common/ROR */

val ROR : forall 'N, 'N >= 1. (bits('N), uinteger) -> bits('N)
function ROR(x, shift) =  {
  /*assert shift >= 0;*/
  result : bits('N) = Zeros();
  if shift == 0 then
    result = x
  else
    let (result', _) = ROR_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/ROR_C */


function ROR_C(x, shift) =
{
  let N = (length(x)) in {
  /* assert shift != 0; */
  m = mod (shift,N);
  result : bits('N) = (LSR(x,m) | LSL(x,N - m));
  carry_out : bit = result[N - 1];
  (result, carry_out);
}}

/** FUNCTION:shared/functions/common/Replicate */

function Replicate (N,x) = {
  let M = length(x);
  assert(mod(N, M) == 0);

  result : bits('N) = Zeros();
  zeros : bits('N-'M) = Zeros();
  foreach (i from M to N by M) result = ((((result << M) : bits('N)) | ((zeros@x) : bits('N))) : bits('N));

  result;
}

/** FUNCTION:integer SInt(bits(N) x) */

/*function forall Nat 'N, Nat 'M, Nat 'K, 'M = 'N + -1, 'K = 2**'M. [|'K * -1:'K + -1|] SInt((bits('N)) x) =*/
function SInt(x) = { 
  signed(x)
  /*let N = (length((bits('N)) 0)) in {
  (integer) result = (nat) x;
  if x[N - 1] == 1 then result = result - (2 ** N);
  result;
}*/}


/** FUNCTION:bits(N) SignExtend(bits(M) x, integer N) */

function SignExtend (N, x : bits('M)) = {
  let M = length(x); /* necessary for the type system to rewrite sizeof */
  let h = x[M - 1];
  (Replicate([h]) : bits(('N - 'M))) @ x
}


/** FUNCTION:integer UInt(bits(N) x) */

function UInt (x : bits('N)) =
  unsigned(x)

/** FUNCTION:bits(N) ZeroExtend(bits(M) x, integer N) */

function ZeroExtend (N, x : bits('M)) = {
  let M = length(x);
  (Zeros() : bits(('N - 'M))) @ x
}

/** FUNCTION:shared/functions/common/Zeros */

function Zeros(N) = (replicate_bits(0b0, 'N)) : bits('N) /* ARM: Zeros(N) */

/** FUNCTION:bits(N) BitReverse(bits(N) data) */

val BitReverse : forall 'N, 'N >= 0. bits('N) -> bits('N)
function BitReverse(data) = {
  let N = (length(data)) in {
  result : bits('N) = Zeros(); /* ARM: uninitialized */
  foreach (i from 0 to (N - 1))
    result[N - i - 1] = data[i];
  result;
}}

/** FUNCTION:shared/functions/crc/HaveCRCExt */

/* TODO: this should not be hardcoded */
function HaveCRCExt() -> boolean = IMPLEMENTATION_DEFINED.HaveCRCExt

/** FUNCTION:bits(32) Poly32Mod2(bits(N) data, bits(32) poly) */

val Poly32Mod2 : forall 'N, 'N >= 0. (bits('N), bits(32)) -> bits(32) effect {escape}
function Poly32Mod2(data, poly) = {
  result : bits('N) = data;
  let N = (length(data)) in {
  assert(N > 32);
  data' : bits('N) = data;
  /* zeros : bits('N - 32) = Zeros(); */
  foreach (i from (N - 1) downto 32) {
    if data'[i] == b1 then
      data'[(i - 1)..0] = data'[(i - 1)..0] ^ (poly@Zeros(i - 32)); /* making this match ASL-generated spec */
  };
  data'[31..0];
}}

/** FUNCTION:shared/functions/exclusive/ClearExclusiveByAddress */

val ClearExclusiveByAddress : (FullAddress, integer, uinteger) -> unit effect pure
function ClearExclusiveByAddress(paddress, processorid, size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

/** FUNCTION:shared/functions/exclusive/ClearExclusiveLocal */

val ClearExclusiveLocal : int -> unit effect pure
function ClearExclusiveLocal(processorid) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

/** FUNCTION:shared/functions/exclusive/ExclusiveMonitorsStatus */

val ExclusiveMonitorsStatus : unit -> bit effect {escape}
function ExclusiveMonitorsStatus() =
{
  info("The model does not implement the exclusive monitors explicitly.");
  not_implemented("ExclusiveMonitorsStatus should not be called");
  /* b0; */
}

/** FUNCTION:shared/functions/exclusive/IsExclusiveGlobal */

val IsExclusiveGlobal : (FullAddress, integer, uinteger) -> boolean effect pure
function IsExclusiveGlobal(paddress, processorid, size) = {
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

/** FUNCTION:shared/functions/exclusive/IsExclusiveLocal */

val IsExclusiveLocal : (FullAddress, integer, uinteger) -> boolean effect pure
function IsExclusiveLocal(paddress, processorid, size) = {
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

/** FUNCTION:shared/functions/exclusive/MarkExclusiveGlobal */

val MarkExclusiveGlobal : (FullAddress, integer, uinteger) -> unit effect pure
function MarkExclusiveGlobal(paddress, processorid, size) = {
  info("The model does not implement the exclusive monitors explicitly.");
}

/** FUNCTION:shared/functions/exclusive/MarkExclusiveLocal */

val MarkExclusiveLocal : (FullAddress, integer, uinteger) -> unit effect pure
function MarkExclusiveLocal(paddress, processorid, size) = {
  info("The model does not implement the exclusive monitors explicitly.");
}

/** FUNCTION:shared/functions/exclusive/ProcessorID */

/* FIXME: return the real number? */
function ProcessorID() -> int = 0

/** FUNCTION:(bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in) */

val AddWithCarry : forall 'N, 'N > 0. (bits('N), bits('N), bit) -> (bits('N), bits(4)) effect {escape}
function AddWithCarry (x, y, carry_in) = {
  unsigned_sum : uinteger = UInt(x) + UInt(y) + UInt([carry_in]);
  signed_sum : integer = SInt(x) + SInt(y) + UInt([carry_in]);
  result : bits('N) = __GetSlice_int('N, unsigned_sum, 0); /* same value as signed_sum<N-1:0> */
  n : bit = result[(length(result)) - 1];
  z : bit = if IsZero(result) then b1 else b0;
  c : bit = if UInt(result) == unsigned_sum then b1 else b0;
  v : bit = if SInt(result) == signed_sum then b1 else b0;
  (result,[n,z,c,v])
  /* (result,[n]:[z]:[c]:[v]) */
}

/** TYPE:shared/functions/memory/AddressDescriptor */
/** FUNCTION:boolean BigEndian() */

val BigEndian : unit -> boolean effect {rreg,escape}
function BigEndian() = {
    /* bigend : boolean = b0; /\* ARM: uninitialized *\/ */
    if UsingAArch32() then
        /* bigend =  */(PSTATE_E != 0b0)
    else if PSTATE_EL() == EL0 then
        /* bigend =  */(SCTLR_EL1.E0E() != 0b0)
    else
        /* bigend =  */((SCTLR'()).EE() != 0b0);
    /* bigend; */
}

/** FUNCTION:shared/functions/memory/BigEndianReverse */
val BigEndianReverse : forall 'W, 'W in {8,16,32,64,128}. bits('W) -> bits('W) effect pure
function BigEndianReverse (value) = {
    let 'half = 'W / 2;
    width : int('W) = length(value);
    /* half : uinteger = width / 2; */
    if width == 8 then value
    else {
      let a = BigEndianReverse(value[('half - 1)..0]);
      let b = BigEndianReverse(value[(width - 1)..half]);
      a @ b;
    }
}

/** FUNCTION:shared/functions/memory/DataMemoryBarrier */

/* external */ val DataMemoryBarrier_NonShReads    : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_NonShWrites   : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_NonShAll      : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_InnerShReads  : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_InnerShWrites : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_InnerShAll    : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_OuterShReads  : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_OuterShWrites : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_OuterShAll    : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_FullShReads   : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_FullShWrites  : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_FullShAll     : unit -> unit effect {barr}

function DataMemoryBarrier_NonShReads()    = __barrier(Barrier_DMB (A64_NonShare,   A64_barrier_LD))
function DataMemoryBarrier_NonShWrites()   = __barrier(Barrier_DMB (A64_NonShare,   A64_barrier_ST))
function DataMemoryBarrier_NonShAll()      = __barrier(Barrier_DMB (A64_NonShare,   A64_barrier_all))
function DataMemoryBarrier_InnerShReads()  = __barrier(Barrier_DMB (A64_InnerShare, A64_barrier_LD))
function DataMemoryBarrier_InnerShWrites() = __barrier(Barrier_DMB (A64_InnerShare, A64_barrier_ST))
function DataMemoryBarrier_InnerShAll()    = __barrier(Barrier_DMB (A64_InnerShare, A64_barrier_all))
function DataMemoryBarrier_OuterShReads()  = __barrier(Barrier_DMB (A64_OuterShare, A64_barrier_LD))
function DataMemoryBarrier_OuterShWrites() = __barrier(Barrier_DMB (A64_OuterShare, A64_barrier_ST))
function DataMemoryBarrier_OuterShAll()    = __barrier(Barrier_DMB (A64_OuterShare, A64_barrier_all))
function DataMemoryBarrier_FullShReads()   = __barrier(Barrier_DMB (A64_FullShare,  A64_barrier_LD))
function DataMemoryBarrier_FullShWrites()  = __barrier(Barrier_DMB (A64_FullShare,  A64_barrier_ST))
function DataMemoryBarrier_FullShAll()     = __barrier(Barrier_DMB (A64_FullShare,  A64_barrier_all))

val DataMemoryBarrier : (MBReqDomain, MBReqTypes) -> unit effect {barr, escape}
function DataMemoryBarrier(domain, types) =
{
  match (domain, types) {
    (MBReqDomain_Nonshareable, MBReqTypes_Reads)  => DataMemoryBarrier_NonShReads(),
    (MBReqDomain_Nonshareable, MBReqTypes_Writes) => DataMemoryBarrier_NonShWrites(),
    (MBReqDomain_Nonshareable, MBReqTypes_All)    => DataMemoryBarrier_NonShAll(),

    (MBReqDomain_InnerShareable, MBReqTypes_Reads)  => DataMemoryBarrier_InnerShReads(),
    (MBReqDomain_InnerShareable, MBReqTypes_Writes) => DataMemoryBarrier_InnerShWrites(),
    (MBReqDomain_InnerShareable, MBReqTypes_All)    => DataMemoryBarrier_InnerShAll(),

    (MBReqDomain_OuterShareable, MBReqTypes_Reads)  => DataMemoryBarrier_OuterShReads(),
    (MBReqDomain_OuterShareable, MBReqTypes_Writes) => DataMemoryBarrier_OuterShWrites(),
    (MBReqDomain_OuterShareable, MBReqTypes_All)    => DataMemoryBarrier_OuterShAll(),

    (MBReqDomain_FullSystem, MBReqTypes_Reads)  => DataMemoryBarrier_FullShReads(),
    (MBReqDomain_FullSystem, MBReqTypes_Writes) => DataMemoryBarrier_FullShWrites(),
    (MBReqDomain_FullSystem, MBReqTypes_All)    => DataMemoryBarrier_FullShAll()
  };
}

/** FUNCTION:shared/functions/memory/DataSynchronizationBarrier */

/* external */ val DataSynchronizationBarrier_NonShReads    : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_NonShWrites   : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_NonShAll      : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_InnerShReads  : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_InnerShWrites : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_InnerShAll    : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_OuterShReads  : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_OuterShWrites : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_OuterShAll    : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_FullShReads   : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_FullShWrites  : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_FullShAll     : unit -> unit effect {barr}

function DataSynchronizationBarrier_NonShReads()    = __barrier(Barrier_DSB (A64_NonShare,   A64_barrier_LD))
function DataSynchronizationBarrier_NonShWrites()   = __barrier(Barrier_DSB (A64_NonShare,   A64_barrier_ST))
function DataSynchronizationBarrier_NonShAll()      = __barrier(Barrier_DSB (A64_NonShare,   A64_barrier_all))
function DataSynchronizationBarrier_InnerShReads()  = __barrier(Barrier_DSB (A64_InnerShare, A64_barrier_LD))
function DataSynchronizationBarrier_InnerShWrites() = __barrier(Barrier_DSB (A64_InnerShare, A64_barrier_ST))
function DataSynchronizationBarrier_InnerShAll()    = __barrier(Barrier_DSB (A64_InnerShare, A64_barrier_all))
function DataSynchronizationBarrier_OuterShReads()  = __barrier(Barrier_DSB (A64_OuterShare, A64_barrier_LD))
function DataSynchronizationBarrier_OuterShWrites() = __barrier(Barrier_DSB (A64_OuterShare, A64_barrier_ST))
function DataSynchronizationBarrier_OuterShAll()    = __barrier(Barrier_DSB (A64_OuterShare, A64_barrier_all))
function DataSynchronizationBarrier_FullShReads()   = __barrier(Barrier_DSB (A64_FullShare,  A64_barrier_LD))
function DataSynchronizationBarrier_FullShWrites()  = __barrier(Barrier_DSB (A64_FullShare,  A64_barrier_ST))
function DataSynchronizationBarrier_FullShAll()     = __barrier(Barrier_DSB (A64_FullShare,  A64_barrier_all))

val DataSynchronizationBarrier : (MBReqDomain, MBReqTypes) -> unit effect {barr,escape}
function DataSynchronizationBarrier(domain, types) =
{
  match (domain, types) {
    (MBReqDomain_Nonshareable, MBReqTypes_Reads)  => DataSynchronizationBarrier_NonShReads(),
    (MBReqDomain_Nonshareable, MBReqTypes_Writes) => DataSynchronizationBarrier_NonShWrites(),
    (MBReqDomain_Nonshareable, MBReqTypes_All)    => DataSynchronizationBarrier_NonShAll(),

    (MBReqDomain_InnerShareable, MBReqTypes_Reads)  => DataSynchronizationBarrier_InnerShReads(),
    (MBReqDomain_InnerShareable, MBReqTypes_Writes) => DataSynchronizationBarrier_InnerShWrites(),
    (MBReqDomain_InnerShareable, MBReqTypes_All)    => DataSynchronizationBarrier_InnerShAll(),

    (MBReqDomain_OuterShareable, MBReqTypes_Reads)  => DataSynchronizationBarrier_OuterShReads(),
    (MBReqDomain_OuterShareable, MBReqTypes_Writes) => DataSynchronizationBarrier_OuterShWrites(),
    (MBReqDomain_OuterShareable, MBReqTypes_All)    => DataSynchronizationBarrier_OuterShAll(),

    (MBReqDomain_FullSystem, MBReqTypes_Reads)  => DataSynchronizationBarrier_FullShReads(),
    (MBReqDomain_FullSystem, MBReqTypes_Writes) => DataSynchronizationBarrier_FullShWrites(),
    (MBReqDomain_FullSystem, MBReqTypes_All)    => DataSynchronizationBarrier_FullShAll()
  };
}

/** ENUMERATE:shared/functions/memory/DeviceType */
/** ENUMERATE:shared/functions/memory/DeviceType */
/** TYPE:shared/functions/memory/FaultRecord */
/** TYPE:shared/functions/memory/FullAddress */
/** FUNCTION:shared/functions/memory/Hint_Prefetch */
val Hint_Prefetch : (bits(64),PrefetchHint,integer,boolean) -> unit effect pure
function Hint_Prefetch(addr,hint,target,stream) = ()
/** ENUMERATE:shared/functions/memory/MBReqDomain */
/** ENUMERATE:shared/functions/memory/MBReqTypes */
/** TYPE:shared/functions/memory/MemAttrHints */
/** ENUMERATE:shared/functions/memory/MemType */
/** TYPE:shared/functions/memory/MemoryAttributes */
/** ENUMERATE:shared/functions/memory/PrefetchHint */
/** FUNCTION:shared/functions/memory/_Mem */

/* regular load */
/* external */ val rMem_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,int('N) /*size*/) -> bits('N*8) effect {rmem}
function rMem_NORMAL (address, size) = __read_mem(Read_plain, 64, address, size)
/* non-temporal load (LDNP), see ARM ARM for special exception to normal memory ordering rules */
/* external */ val rMem_STREAM : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,int('N) /*size*/) -> bits('N*8) effect {rmem}
function rMem_STREAM (address, size) = __read_mem(Read_stream, 64, address, size)
/* load-acquire */
/* external */ val rMem_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,int('N) /*size*/) -> bits('N*8) effect {rmem}
function rMem_ORDERED (address, size) = __read_mem(Read_acquire, 64, address, size)
/* load-exclusive */
/* external */ val rMem_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,int('N) /*size*/) -> bits('N*8) effect {rmem}
function rMem_ATOMIC (address, size) = __read_mem(Read_exclusive, 64, address, size)
/* load-exclusive+acquire */
/* external */ val rMem_ATOMIC_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,int('N) /*size*/) -> bits('N*8) effect {rmem}
function rMem_ATOMIC_ORDERED (address, size) = __read_mem(Read_exclusive_acquire, 64, address, size)

struct read_buffer_type = {
  acctype : AccType,
  exclusive : bool,
  address : bits(64),
  size : uinteger,
}

let empty_read_buffer : read_buffer_type = 
  struct { 
    size = 0,
    /* arbitrary values: */
    acctype = AccType_NORMAL,
    exclusive = false,
    address = Zeros()
  }

val _rMem : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, AddressDescriptor, int('N), AccType, bool) -> read_buffer_type effect {escape}
function _rMem(read_buffer, desc, size, acctype, exclusive) = {
  if read_buffer.size == 0 then 
    struct { acctype = acctype,
      exclusive = exclusive,
      address = (desc.paddress).physicaladdress,
      size = size
    }
  else {
    assert(read_buffer.acctype == acctype);
    assert(read_buffer.exclusive == exclusive);
    assert((read_buffer.address + read_buffer.size) : bits(64) == (desc.paddress).physicaladdress);

    {read_buffer with size = read_buffer.size + size}
  }
}

val flush_read_buffer : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, int('N)) -> bits('N*8) effect {rmem, rreg, escape}
function flush_read_buffer(read_buffer, size) =
{
  assert(read_buffer.size == size);

  value : bits('N*8) = Zeros();

  if read_buffer.exclusive then {
    match read_buffer.acctype {
      AccType_ATOMIC   => value = rMem_ATOMIC(read_buffer.address, size),
      AccType_ORDERED  => value = rMem_ATOMIC_ORDERED(read_buffer.address, size),
      _  => { not_implemented("unimplemented memory access"); }
    }
  } else {
    match read_buffer.acctype {
      AccType_NORMAL   => value = rMem_NORMAL (read_buffer.address, size),
      AccType_STREAM   => value = rMem_STREAM (read_buffer.address, size),
      AccType_UNPRIV   => value = rMem_NORMAL (read_buffer.address, size),
      AccType_ORDERED  => value = rMem_ORDERED(read_buffer.address, size),
      AccType_ATOMIC   => error("Reached AccType_ATOMIC: unreachable when address values are known"),
        /* (*old code*) value = rMem_NORMAL (read_buffer.address, size) (* the second read of 64-bit LDXP *)*/
      _ => exit()
    }
  };

  if BigEndian() then
    value = BigEndianReverse(value);
  value;
}

/** FUNCTION:_Mem[AddressDescriptor desc, integer size, AccType acctype] = bits(8*size) value; */

/* regular store */
/* external */ val wMem_Addr_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, int('N) /*size*/) -> unit effect {eamem}
function wMem_Addr_NORMAL (address, size) = { __write_mem_ea(Write_plain, 64, address, size); () }
/* store-release */
/* external */ val wMem_Addr_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, int('N) /*size*/) -> unit effect {eamem}
function wMem_Addr_ORDERED (address, size) = { __write_mem_ea(Write_release, 64, address, size); () }
/* store-exclusive */
/* external */ val wMem_Addr_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, int('N) /*size*/) -> unit effect {eamem}
function wMem_Addr_ATOMIC (address, size) = { __write_mem_ea(Write_exclusive, 64, address, size); () }
/* store-exclusive+release */
/* external */ val wMem_Addr_ATOMIC_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, int('N) /*size*/) -> unit effect {eamem}
function wMem_Addr_ATOMIC_ORDERED (address, size) = { __write_mem_ea(Write_exclusive_release, 64, address, size); () }

val wMem_Addr : forall 'N, 'N in {1,2,4,8,16}. (bits(64), int('N), AccType, boolean) -> unit effect {eamem, escape}
function wMem_Addr(address, size, acctype, excl) =
{
  match (excl, acctype) {
    (false, AccType_NORMAL)   => wMem_Addr_NORMAL(address, size),
    (false, AccType_STREAM)   => wMem_Addr_NORMAL(address, size),
    (false, AccType_UNPRIV)   => wMem_Addr_NORMAL(address, size),
    (false, AccType_ORDERED)  => wMem_Addr_ORDERED(address, size),
    (true, AccType_ATOMIC)    => wMem_Addr_ATOMIC(address, size),
    (true, AccType_ORDERED)   => wMem_Addr_ATOMIC_ORDERED(address, size),
    _  => not_implemented("unrecognised memory access")
  };
}


/* regular store */
/* external */ val wMem_Val_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*addr*/, int('N) /*size*/, bits('N*8) /*value*/) -> unit effect {wmv}
function wMem_Val_NORMAL (address, size, value) = { let b = __write_mem(Write_plain, 64, address, size, value); () }
/* external */ val wMem_Val_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*addr*/, int('N) /*size*/, bits('N*8) /*value*/) -> unit effect {wmv}
function wMem_Val_ORDERED (address, size, value) = { let b = __write_mem(Write_release, 64, address, size, value); () }
/* store-exclusive */
/* external */ val wMem_Val_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*addr*/, int('N) /*size*/, bits('N*8) /*value*/) -> bool effect {wmv}
function wMem_Val_ATOMIC (address, size, value) = __write_mem(Write_exclusive, 64, address, size, value)
/* external */ val wMem_Val_ATOMIC_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*addr*/, int('N) /*size*/, bits('N*8) /*value*/) -> bool effect {wmv}
function wMem_Val_ATOMIC_ORDERED (address, size, value) = __write_mem(Write_exclusive_release, 64, address, size, value)


struct write_buffer_type = {
  acctype : AccType,
  exclusive : bool,
  address : bits(64),
  value : bits(128),
  /* size : uinteger, */
  size : range(0,16),
}

let empty_write_buffer : write_buffer_type = struct { 
  size = 0,
  /* arbitrary values: */
  acctype = AccType_NORMAL,
  exclusive = false,
  address = Zeros(),
  value = Zeros()
}

val _wMem : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, AddressDescriptor, int('N), AccType, bool, bits('N*8)) -> write_buffer_type effect {escape}
function _wMem(write_buffer, desc, size, acctype, exclusive, value) = {
  let s = write_buffer.size;
  if s == 0 then {
    struct { acctype = acctype,
      exclusive = exclusive,
      address = (desc.paddress).physicaladdress,
      value = ZeroExtend(value),
      size = size
    }
  } else {
    assert(write_buffer.acctype == acctype);
    assert(write_buffer.exclusive == exclusive);
    assert((write_buffer.address + s) : bits(64) == (desc.paddress).physicaladdress);
  assert((s * 8) + ('N * 8) <= 128);
    { write_buffer with
      value = (ZeroExtend(value @ (write_buffer.value)[((s * 8) - 1) .. 0])),
      size = s + size
    }
  }
}

val flush_write_buffer : write_buffer_type -> unit effect {escape, wmv}
function flush_write_buffer(write_buffer) = {
  assert(write_buffer.exclusive == false);
  let s : range(0,16) = write_buffer.size;
  assert (s == 1 | s == 2 | s == 4 | s == 8 | s == 16);
  match write_buffer.acctype {
    AccType_NORMAL   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_STREAM   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_UNPRIV   => wMem_Val_NORMAL (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_ORDERED (write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    _  => not_implemented("unrecognised memory access")
  };
}

val flush_write_buffer_exclusive : write_buffer_type -> bool effect {escape, wmv}
function flush_write_buffer_exclusive(write_buffer) = {
  assert(write_buffer.exclusive);
  let s = write_buffer.size;
  assert (s == 1 | s == 2 | s == 4 | s == 8 | s == 16);
  match write_buffer.acctype {
    AccType_ATOMIC   => wMem_Val_ATOMIC(write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_ATOMIC_ORDERED(write_buffer.address, s, (write_buffer.value)[((s * 8) - 1) .. 0]),
    _  => { not_implemented("unrecognised memory access"); false; }
  };
}

/** FUNCTION:BranchTo(bits(N) target, BranchType branch_type) */

val BranchTo : forall 'N, 'N in {32,64}. (bits('N), BranchType) -> unit effect {escape, rreg, wreg}
function BranchTo(target, branch_type) = {
  target' : bits('N) = target; /* Sail does not let you change parameter vector */

  Hint_Branch(branch_type);
  if length(target) == 32 then {
    assert( UsingAArch32());
    _PC = ZeroExtend(target);
  } else {
    assert( length(target) == 64 & ~(UsingAArch32()) );
    /* Remove the tag bits from tagged target */
    let pstate_el = PSTATE_EL() in {
      if pstate_el == EL0 then {
        if target'[55] == b1 & TCR_EL1.TBI1() == 0b1 then
          target'[63..56] = 0b11111111;
        if target'[55] == b0 & TCR_EL1.TBI0() == 0b1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL1 then {
        if target'[55] == b1 & TCR_EL1.TBI1() == 0b1 then
          target'[63..56] = 0b11111111;
        if target'[55] == b0 & TCR_EL1.TBI0() == 0b1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL2 then {
        if TCR_EL2.TBI() == 0b1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL3 then {
        if TCR_EL3.TBI() == 0b1 then
          target'[63..56] = 0b00000000;
      }
      else exit()
    };
    _PC = target';
  };
}

/** ENUMERATE:shared/functions/registers/BranchType */
/** FUNCTION:shared/functions/registers/Hint_Branch */

val Hint_branch : BranchType -> unit effect pure
function Hint_Branch(hint) = {
  info("This hint can be used for hardware optimization that has no effect on the model.");
}

/** FUNCTION:shared/functions/registers/ResetExternalDebugRegisters */
val ResetExternalDebugRegisters : boolean -> unit effect {escape}
function ResetExternalDebugRegisters (b) = 
  not_implemented_extern("ResetExternalDebugRegisters")
/** FUNCTION:shared/functions/registers/ThisInstrAddr */

val ThisInstrAddr : forall 'N, 'N >= 0. implicit('N) -> bits('N) effect {escape,rreg}
function ThisInstrAddr(N) = {
  assert(N == 64 | (N == 32 & UsingAArch32()));
  /*return*/ mask(rPC());
}

/** FUNCTION:// SPSR[] - non-assignment form */

function rSPSR() -> bits(32) = {
  /* result : bits(32) = Zeros(); /\* ARM: uninitialized *\/ */
  if UsingAArch32() then {
    not_implemented("rSPSR UsingAArch32");
    /* ARM:
    case PSTATE.M of
      when M32_FIQ       result = SPSR_fiq;
      when M32_IRQ       result = SPSR_irq;
      when M32_Svc       result = SPSR_svc;
      when M32_Monitor   result = SPSR_mon;
      when M32_Abort     result = SPSR_abt;
      when M32_Hyp       result = SPSR_hyp;
      when M32_Undef     result = SPSR_und;
      otherwise          Unreachable();
    */
  } else {
    let pstate_el = PSTATE_EL() in {
      if      pstate_el == EL1 then /* result =  */SPSR_EL1.bits()
      else if pstate_el == EL2 then /* result =  */SPSR_EL2.bits()
      else if pstate_el == EL3 then /* result =  */SPSR_EL3.bits()
      else {Unreachable(); Zeros()}
    };
  };
  /* result; */
}

/** FUNCTION:shared/functions/system/ClearEventRegister */
function ClearEventRegister () -> unit = not_implemented_extern("ClearEventRegister")
/** FUNCTION:boolean ConditionHolds(bits(4) cond) */

val ConditionHolds : bits(4) -> boolean effect {rreg}
function ConditionHolds(_cond) = {
  result : boolean = false; /* ARM: uninitialized */
  /* Evaluate base condition */
  match _cond[3..1] {
    0b000  => result = (PSTATE_Z() == 0b1),                        /* EQ or NE */
    0b001  => result = (PSTATE_C() == 0b1),                        /* CS or CC */
    0b010  => result = (PSTATE_N() == 0b1),                        /* MI or PL */
    0b011  => result = (PSTATE_V() == 0b1),                        /* VS or VC */
    0b100  => result = (PSTATE_C() == 0b1 & PSTATE_Z() == 0b0),        /* HI or LS */
    0b101  => result = (PSTATE_N() == PSTATE_V()),                 /* GE or LT */
    0b110  => result = (PSTATE_N() == PSTATE_V() & PSTATE_Z() == 0b0), /* GT or LE */
    0b111  => result = true                                    /* AL */
  };

  /* Condition flag values in the set '111x' indicate always true */
  /* Otherwise, invert condition if necessary. */
  if _cond[0] == b1 & _cond != 0b1111 then
    result = ~(result);

  result;
}

/** ENUMERATE:shared/functions/system/EL0 */
/** FUNCTION:boolean ELUsingAArch32(bits(2) el) */

function ELUsingAArch32(el : bits(2)) -> boolean =
    false /* ARM: ELStateUsingAArch32(el, IsSecureBelowEL3()) */ /* FIXME: implement */

/** FUNCTION:shared/functions/system/EventRegisterSet */
function EventRegisterSet () -> unit = not_implemented_extern("EventRegisterSet")
/** FUNCTION:shared/functions/system/EventRegistered */
function EventRegistered () -> boolean = not_implemented_extern("EventRegistered")
/** FUNCTION:shared/functions/system/HaveAArch32EL */

function HaveAArch32EL (el : bits(2)) -> boolean = {
  /* Return TRUE if Exception level 'el' supports AArch32 */
  if ~(HaveEL(el)) then
    false
  else if ~(HaveAnyAArch32()) then
    false                       /* No exception level can use AArch32    */
  else if HighestELUsingAArch32() then
    true                        /* All exception levels must use AArch32 */
  else if el == EL0 then
    true                        /* EL0 must support using AArch32        */
  else

  IMPLEMENTATION_DEFINED.HaveAArch32EL;
}

/** FUNCTION:boolean HaveAnyAArch32() */

function HaveAnyAArch32() -> boolean =
{
  IMPLEMENTATION_DEFINED.HaveAnyAArch32
}

/** FUNCTION:boolean HaveEL(bits(2) el) */

function HaveEL(el : bits(2)) -> boolean = {
  if el == EL1 | el == EL0 then
    true /*EL1 and EL0 must exist*/
  else {

  if      el == EL2 then IMPLEMENTATION_DEFINED.HaveEL2
  else if el == EL3 then IMPLEMENTATION_DEFINED.HaveEL3
  else exit();
  };
}

/** FUNCTION:boolean HighestELUsingAArch32() */

function HighestELUsingAArch32() -> boolean = {
  if ~(HaveAnyAArch32()) then false else
  IMPLEMENTATION_DEFINED.HighestELUsingAArch32; /* e.g. CFG32SIGNAL == HIGH */
}

/** FUNCTION:shared/functions/system/Hint_Yield */

function Hint_Yield() -> unit = ()

/** FUNCTION:shared/functions/system/InstructionSynchronizationBarrier */
/* external */ val InstructionSynchronizationBarrier : unit -> unit effect {barr}
function InstructionSynchronizationBarrier () = __barrier(Barrier_ISB())
/** FUNCTION:shared/functions/system/InterruptPending */

function InterruptPending () -> boolean = not_implemented_extern("InterruptPending")

/** FUNCTION:boolean IsSecure() */

function IsSecure() -> boolean = {
  /*Return TRUE if current Exception level is in Secure state.*/
  if HaveEL(EL3) & ~(UsingAArch32()) & PSTATE_EL() == EL3 then
    true
  else if HaveEL(EL3) & UsingAArch32() & PSTATE_M == M32_Monitor then
    true
  else
    IsSecureBelowEL3();
}

/** FUNCTION:boolean IsSecureBelowEL3() */

function IsSecureBelowEL3() -> boolean = {
  if HaveEL(EL3) then
    SCR_GEN().NS() == 0b0
  else if HaveEL(EL2) then
    false
  else
    /*TRUE if processor is Secure or FALSE if Non-secure;*/
    IMPLEMENTATION_DEFINED.IsSecureBelowEL3;
}

/** ENUMERATE:shared/functions/system/Mode_Bits */
/** FUNCTION:shared/functions/system/SCR_GEN */

function SCR_GEN() -> SCRType = {
  /*AArch32 secure & AArch64 EL3 registers are not architecturally mapped*/
  assert (HaveEL(EL3));

  if HighestELUsingAArch32() then
    SCR
  else
    SCR_EL3;
}

/** FUNCTION:shared/functions/system/SendEvent */

function SendEvent() -> unit =
{
  ()
  /* TODO: ??? */
}


/** FUNCTION:shared/functions/system/UsingAArch32 */

function UsingAArch32() -> boolean =
{
  false;
  /* ARM: uncomment when implementing aarch32
  boolean aarch32 = (PSTATE.nRW == '1');
  if !HaveAnyAArch32() then assert !aarch32;
  if HighestELUsingAArch32() then assert aarch32;
  return aarch32;*/
}

/** FUNCTION:shared/functions/system/WaitForEvent */
function WaitForEvent () -> unit = not_implemented_extern("WaitForEvent")
/** FUNCTION:shared/functions/system/WaitForInterrupt */
function WaitForInterrupt () -> unit  = not_implemented_extern("WaitForInterrupt")
/** FUNCTION:shared/translation/translation/PAMax */

function PAMax() -> range(32,48) = {
  pa_size : range(32,48) = 32;
  match ID_AA64MMFR0_EL1.PARange() {
    0b0000  => pa_size = 32,
    0b0001  => pa_size = 36,
    0b0010  => pa_size = 40,
    0b0011  => pa_size = 42,
    0b0100  => pa_size = 44,
    0b0101  => pa_size = 48,
    _  => Unreachable()
  };

  return pa_size;
}

/** FUNCTION:shared/translation/translation/S1TranslationRegime */

val S1TranslationRegime : unit -> bits(2) effect {escape,rreg}
function S1TranslationRegime () = {
  if PSTATE_EL() != EL0 then
    PSTATE_EL()
  else if IsSecure() & HaveEL(EL3) & ELUsingAArch32(EL3) then
    EL3
  else
    EL1
}

