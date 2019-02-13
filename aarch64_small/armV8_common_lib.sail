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

/** FUNCTION:shared/debug/DoubleLockStatus/DoubleLockStatus */

function boolean DoubleLockStatus() =
{
  if ELUsingAArch32(EL1) then
    (DBGOSDLR.DLK == 1 & DBGPRCR.CORENPDRQ == 0 & ~(Halted()))
  else
    (OSDLR_EL1.DLK == 1 & DBGPRCR_EL1.CORENPDRQ == 0 & ~(Halted()));
}

/** FUNCTION:shared/debug/authentication/Debug_authentication */

/* TODO: these are external signals */

enum signalValue = {LOw, HIGH}

function signalValue signalDBGEN () = not_implemented_extern("signalDBGEN")
function signalValue signelNIDEN () = not_implemented_extern("signalNIDEN")
function signalValue signalSPIDEN () = not_implemented_extern("signalSPIDEN")
function signalValue signalDPNIDEN () = not_implemented_extern("signalSPNIDEN")

/** FUNCTION:shared/debug/authentication/ExternalInvasiveDebugEnabled */

function boolean ExternalInvasiveDebugEnabled() =
{
  /* In the recommended interface, ExternalInvasiveDebugEnabled returns the state of the DBGEN */
  /* signal. */
  signalDBGEN() == HIGH;
}

/** FUNCTION:shared/debug/authentication/ExternalSecureInvasiveDebugEnabled */

function boolean ExternalSecureInvasiveDebugEnabled() =
{
  /* In the recommended interface, ExternalSecureInvasiveDebugEnabled returns the state of the */
  /* (DBGEN AND SPIDEN) signal. */
  /* CoreSight allows asserting SPIDEN without also asserting DBGEN, but this is not recommended. */
  if ~(HaveEL(EL3)) & ~(IsSecure()) then false
  else {
  (ExternalInvasiveDebugEnabled() & signalSPIDEN() == HIGH);
}}

/** FUNCTION:shared/debug/halting/DCPSInstruction */

function unit DCPSInstruction(target_el : bits(2)) =
{
  not_implemented("DCPSInstruction");
}

/** FUNCTION:shared/debug/halting/DRPSInstruction */

function unit DRPSInstruction() =
{
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

function unit Halt(reason : bits(6)) =
{
  not_implemented("Halt");
}

/** FUNCTION:shared/debug/halting/Halted */

function boolean Halted() =
{
  ~(EDSCR.STATUS == 0b000001 | EDSCR.STATUS == 0b000010); /* Halted */
}

/** FUNCTION:shared/debug/halting/HaltingAllowed */

function boolean HaltingAllowed() =
{
  if Halted() | DoubleLockStatus() then
    false
  else if IsSecure() then
    ExternalSecureInvasiveDebugEnabled()
  else
    ExternalInvasiveDebugEnabled();
}

/** FUNCTION:shared/exceptions/traps/ReservedValue */

function unit ReservedValue() =
{
  /* ARM: uncomment when adding aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException()
  else*/
    AArch64_UndefinedFault();
}

/** FUNCTION:shared/exceptions/traps/UnallocatedEncoding */

function unit UnallocatedEncoding() =
{
  /* If the unallocated encoding is an AArch32 CP10 or CP11 instruction, FPEXC.DEX must be written */
  /* to zero. This is omitted from this code. */
  /* ARM: uncomment whenimplementing aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException();
  else*/
    AArch64_UndefinedFault();
}

/** FUNCTION:shared/functions/aborts/IsFault */

function boolean IsFault(addrdesc : AddressDescriptor) =
{
    (addrdesc.fault).faulttype != Fault_None;
}

/** FUNCTION:shared/functions/common/ASR */

val ASR : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function ASR (x, shift) = 
{
  /*assert shift >= 0;*/
  result : bits('N) = 0;
  if shift == 0 then
    result = x
  else
    let (result', _) = ASR_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/ASR_C */

val ASR_C : forall 'N 'S, 'N >= 0 & 'S >= 1. (bits('N), atom('S)) -> (bits('N), bit)
function ASR_C (x, shift) = 
{
  /*assert shift > 0;*/
  extended_x : bits('S+'N) = SignExtend(x);
  result : bits('N) = extended_x[(shift + length(x) - 1)..shift];
  carry_out : bit = extended_x[shift - 1];
  (result, carry_out);
}

/** FUNCTION:integer Align(integer x, integer y) */

function uinteger Align'(x : uinteger, y : uinteger) =
    y * (quot (x,y))

/** FUNCTION:bits(N) Align(bits(N) x, integer y) */

val Align : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function Align (x, y) =
    Align'(UInt(x), y) : (bits('N))

/** FUNCTION:integer CountLeadingSignBits(bits(N) x) */

val CountLeadingSignBits : forall 'N, 'N >= 0. bits('N) -> range(0,'N)
function CountLeadingSignBits(x) =
  CountLeadingZeroBits(x[(length(x) - 1)..1] ^ x[(length(x) - 2)..0])

/** FUNCTION:integer CountLeadingZeroBits(bits(N) x) */

val CountLeadingZeroBits : forall 'N, 'N >= 0. bits('N) -> range(0,'N)
function CountLeadingZeroBits(x) =
  match HighestSetBit(x) {
    None  => length(x),
    Some(n)  => length(x) - 1 - n
  }
/** FUNCTION:bits(N) Extend(bits(M) x, integer N, boolean unsigned) */

val Extend : forall 'N 'M, 0 <= 'M & 'M <= 'N. (implicit('N),bits('M),bit) -> bits('N) effect pure
function Extend (x, unsigned) =
  if unsigned then ZeroExtend(x) else SignExtend(x)

/** FUNCTION:integer HighestSetBit(bits(N) x) */

val HighestSetBit : forall 'N, 'N >= 0. bits('N) -> option(range(0, 'N + -1))
function HighestSetBit(x) = {
  let N = (length(x)) in {
  result : range(0, 'N + -1) = 0;
  break : bool = false;
  foreach (i from (N - 1) downto 0)
    if ~(break) & x[i] == 1 then {
      result = i;
      break = true;
    };

  if break then Some(result) else None;
}}

/** FUNCTION:integer Int(bits(N) x, boolean unsigned) */
/* used to be called Int */
val _Int : forall 'N, 'N >= 0. (bits('N), boolean) -> integer
function _Int (x, unsigned) = {
  result = if unsigned then UInt(x) else SInt(x);
  result;
}

/** FUNCTION:boolean IsZero(bits(N) x) */

val IsZero : forall 'N, 'N >= 0. bits('N) -> boolean
function IsZero(x) = x == 0 /* ARM: Zeros(N) */

/** FUNCTION:bit IsZeroBit(bits(N) x) */

val IsZeroBit : forall 'N, 'N >= 0. bits('N) -> bit
function IsZeroBit(x) = if IsZero(x) then 1 else 0

/** FUNCTION:shared/functions/common/LSL */

val LSL : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function LSL(x, shift) =
{
  /*assert shift >= 0;*/
  result : bits('N) = 0;
  if shift == 0 then
    result = x
  else
    let (result',_) = LSL_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/LSL_C */

val LSL_C : forall 'N 'S, 'N >= 0 & 'S >= 1. (bits('N), atom('S)) -> (bits('N))
function LSL_C (x, shift) =
{
  /*assert shift > 0;*/
  extended_x : bits('N + 'S) = x @ ((Zeros()) : (bits('S)));
  result : bits('N) = mask(extended_x);
  carry_out : bit = extended_x[length(x)];
  (result, carry_out);
}

/** FUNCTION:shared/functions/common/LSR */

val LSR : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function LSR(x, shift) =
{
  /*assert shift >= 0;*/
  result : bits('N) = 0;
  if shift == 0 then
    result = x
  else
    let (result', _) = LSR_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/LSR_C */

val LSR_C : forall 'N 'S, 'N >= 0 & 'S >=1. (bits('N), atom('S)) -> (bits('N), bit)
function LSR_C(x, shift) =
{
  /*assert shift > 0;*/
  extended_x : bits('N + 'S) = ZeroExtend(x);
  result : bits('N) = extended_x[(shift + length(x) - 1)..shift];
  carry_out : bit = extended_x[shift - 1];
  (result, carry_out);
}

/** FUNCTION:integer Min(integer a, integer b) */

val Min : (integer, integer) -> integer
function Min (a,b) =
  if a <= b then a else b

val uMin : (uinteger, uinteger) -> uinteger
function uMin (a,b) =
  if a <= b then a else b

/** FUNCTION:bits(N) NOT(bits(N) x); */

val NOT : forall 'N, 'N >= 0. bits('N) -> bits('N)
function NOT(x) = ~(x)

val NOT' : bit -> bit
function NOT'(x) = ~(x)

/** FUNCTION:shared/functions/common/Ones */

val Ones : forall 'N, 'N >= 0. unit -> bits('N)
function Ones() = Replicate([1])

/** FUNCTION:shared/functions/common/ROR */

val ROR : forall 'N, 'N >= 0. (bits('N), uinteger) -> bits('N)
function ROR(x, shift) = 
{
  /*assert shift >= 0;*/
  result : bits('N) = 0;
  if shift == 0 then
    result = x
  else
    let (result', _) = ROR_C (x, shift) in { result = result' };
  result;
}

/** FUNCTION:shared/functions/common/ROR_C */

val ROR_C : forall 'N 'S, 'N >= 0 & ('S >=1 | 'S <= -1). (bits('N), atom('S)) -> (bits('N))
function ROR_C(x, shift) =
{
  let N = (length(x)) in {
  /*assert shift != 0;*/
  m : nat = mod (shift,N);
  result : bits('N) = (LSR(x,m) | LSL(x,N - m));
  carry_out : bit = result[N - 1];
  (result, carry_out);
}}

/** FUNCTION:shared/functions/common/Replicate */

val Replicate : forall 'N 'M, 'N >= 0 & 'M >= 0. bits('M) -> bits('N)
function Replicate (x) = {
  let (N,M) : (bits('N),bits('M)) = (0,0) in {
  assert((mod(N, M) == 0),None);

  result : bits('N) = 0;
  zeros : bits('N-'M) = (Zeros());
  foreach (i from M to N by M) result = ((result << M) | zeros:x);

  result;
}}

/** FUNCTION:integer SInt(bits(N) x) */

/*function forall Nat 'N, Nat 'M, Nat 'K, 'M = 'N + -1, 'K = 2**'M. [|'K * -1:'K + -1|] SInt((bits('N)) x) =*/
val SInt : forall 'N 'M, 'N >= 0 & 'M >= 0. bits('N) -> atom('M)
function SInt(x) = { 
  signed(x)
  /*let N = (length((bits('N)) 0)) in {
  (integer) result = (nat) x;
  if x[N - 1] == 1 then result = result - (2 ** N);
  result;
}*/}


/** FUNCTION:bits(N) SignExtend(bits(M) x, integer N) */

val SignExtend : forall 'N 'M, 'N >= 0 & 'M >= 1. bits('M) -> bits('N)
function SignExtend ([h]:remainder as x) =
  (Replicate([h]) : bits(('N - 'M))) @ x

/** FUNCTION:integer UInt(bits(N) x) */

/* function forall Nat 'N, Nat 'M, 'M = 2**'N. [|'M + -1|] UInt((bits('N)) x) = ([|'M + -1|]) x */
val Uint : forall 'M 'N, 'M >= 0 & 'N >= 0. bits('N) -> atom('M)
function UInt(x) = unsigned(x)

/** FUNCTION:bits(N) ZeroExtend(bits(M) x, integer N) */

val ZeroExtend : forall 'M 'N, 'M >= 0 & 'N >= 0. bits('M) -> bits('N)
function ZeroExtend (x) = (Zeros() : bits(('N + 'M * -1))) @ x

/** FUNCTION:shared/functions/common/Zeros */

val Zeros : forall 'N, 'N >= 0. unit -> bits('N)
function Zeros() = 0 : bits('N) /* ARM: Zeros(N) */

/** FUNCTION:bits(N) BitReverse(bits(N) data) */

val BitReverse : forall 'N, 'N >= 0. bits('N) -> bits('N)
function BitReverse(data) = {
  let N = (length(data)) in {
  result : bits('N) = 0; /* ARM: uninitialized */
  foreach (i from 0 to (N - 1))
    result[N - i - 1] = data[i];
  result;
}}

/** FUNCTION:shared/functions/crc/HaveCRCExt */

/* TODO: this should not be hardcoded */
function HaveCRCExt() -> boolean = IMPLEMENTATION_DEFINED.HaveCRCExt

/** FUNCTION:bits(32) Poly32Mod2(bits(N) data, bits(32) poly) */

val Poly32Mod2 : forall 'N, 'N >= 0. (bits('N), bits(32)) -> bits(32)
function Poly32Mod2(data, poly) = {
  result : bits('N) = data;
  let N = (length(data)) in {
  assert((N > 32 ),None);
  data' : bits('N) = data;
  zeros : bits('N - 32) = Zeros();
  foreach (i from (N - 1) downto 32) {
    if data'[i] == 1 then
      data'[(i - 1)..0] = data'[(i - 1)..0] ^ (poly:zeros[(i - 33)..0]);
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

val ExclusiveMonitorsStatus : unit -> bit effect pure
function ExclusiveMonitorsStatus() =
{
  info("The model does not implement the exclusive monitors explicitly.");
  not_implemented("ExclusiveMonitorsStatus should not be called");
  0;
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
function integer ProcessorID() = {0}

/** FUNCTION:(bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in) */

val AddWithCarry : forall 'N, 'N >= 0. (bits('N), bits('N), bit) -> (bits('N), bits(4))
function AddWithCarry (x, y, carry_in) = {
  unsigned_sum : uinteger = UInt(x) + UInt(y) + UInt([carry_in]);
  signed_sum : integer = SInt(x) + SInt(y) + UInt([carry_in]);
  result : bits('N) =  unsigned_sum; /* same value as signed_sum<N-1:0> */
  n : bit = result[(length(result)) - 1];
  z : bit = if IsZero(result) then 1 else 0;
  c : bit = if UInt(result) == unsigned_sum then 0 else 1;
  v : bit = if SInt(result) == signed_sum then 0 else 1;
  (result,[n,z,c,v])
  /* (result,[n]:[z]:[c]:[v]) */
}

/** TYPE:shared/functions/memory/AddressDescriptor */
/** FUNCTION:boolean BigEndian() */

val BigEndian : unit -> boolean effect {rreg}
function BigEndian() = {
    bigend : boolean = 0; /* ARM: uninitialized */
    if UsingAArch32() then
        bigend = (PSTATE_E != 0)
    else if PSTATE_EL == EL0 then
        bigend = (SCTLR_EL1.E0E != 0)
    else
        bigend = ((SCTLR'()).EE != 0);
    bigend;
}

/** FUNCTION:shared/functions/memory/BigEndianReverse */
val BigEndianReverse : forall 'W, 'W in {8,16,32,64,128}. bits('W) -> bits('W) effect pure
function rec BigEndianReverse (value) =
{
    width : uinteger= length(value);
    half : uinteger = quot(width,2);
    if width == 8 then /*return*/ value
    else /*return*/ BigEndianReverse(value[(half - 1)..0]) @ BigEndianReverse(value[(width - 1)..half]);
}

/** FUNCTION:shared/functions/memory/DataMemoryBarrier */

/* external */ val DataMemoryBarrier_Reads : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_Writes : unit -> unit effect {barr}
/* external */ val DataMemoryBarrier_All : unit -> unit effect {barr}

val DataMemoryBarrier : (MBReqDomain, MBReqTypes) -> unit effect {barr}
function DataMemoryBarrier(domain, types) =
{
  if domain != MBReqDomain_FullSystem & domain != MBReqDomain_InnerShareable then
    not_implemented("DataMemoryBarrier: not MBReqDomain_FullSystem or _InnerShareable");

  match types {
    MBReqTypes_Reads   => DataMemoryBarrier_Reads(),
    MBReqTypes_Writes  => DataMemoryBarrier_Writes(),
    MBReqTypes_All     => DataMemoryBarrier_All()
  };
}

/** FUNCTION:shared/functions/memory/DataSynchronizationBarrier */

/* external */ val DataSynchronizationBarrier_Reads : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_Writes : unit -> unit effect {barr}
/* external */ val DataSynchronizationBarrier_All : unit -> unit effect {barr}

val DataSynchronizationBarrier : (MBReqDomain, MBReqTypes) -> unit effect {barr}
function DataSynchronizationBarrier(domain, types) =
{
  if domain != MBReqDomain_FullSystem then
    not_implemented("DataSynchronizationBarrier: not MBReqDomain_FullSystem");

  match types {
    MBReqTypes_Reads   => DataSynchronizationBarrier_Reads(),
    MBReqTypes_Writes  => DataSynchronizationBarrier_Writes(),
    MBReqTypes_All     => DataSynchronizationBarrier_All()
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
/* external */ val rMem_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,atom('N) /*size*/) -> bits('N*8) effect {rmem}
/* non-temporal load (LDNP), see ARM ARM for special exception to normal memory ordering rules */
/* external */ val rMem_STREAM : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,atom('N) /*size*/) -> bits('N*8) effect {rmem}
/* load-acquire */
/* external */ val rMem_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,atom('N) /*size*/) -> bits('N*8) effect {rmem}
/* load-exclusive */
/* external */ val rMem_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,atom('N) /*size*/) -> bits('N*8) effect {rmem}
/* load-exclusive+acquire */
/* external */ val rMem_ATOMIC_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/,atom('N) /*size*/) -> bits('N*8) effect {rmem}

struct read_buffer_type = {
  acctype : AccType,
  exclusive : bool,
  address : bits(64),
  size : uinteger,
}

let empty_read_buffer =
{ size = 0;
  /* arbitrary values: */
  acctype = AccType_NORMAL;
  exclusive = false;
  address = 0;
}

val _rMem : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, AddressDescriptor, atom('N), AccType, bool) -> read_buffer_type effect pure
function _rMem(read_buffer, desc, size, acctype, exclusive) = {
  if read_buffer.size == 0 then {
    { acctype = acctype;
      exclusive = exclusive;
      address = (desc.paddress).physicaladdress;
      size = size;
    }
  }
  else {
    assert((read_buffer.acctype == acctype), None);
    assert((read_buffer.exclusive == exclusive), None);
    assert(((read_buffer.address + read_buffer.size) : bits(64) == (desc.paddress).physicaladdress), None);

    {read_buffer with size = read_buffer.size + size}
  }
}

val flush_read_buffer : forall 'N, 'N in {1,2,4,8,16}. (read_buffer_type, atom('N)) -> bits('N*8)
function flush_read_buffer(read_buffer, size) =
{
  assert((read_buffer.size == size), None);

  value : bits('N*8) = 0;

  if read_buffer.exclusive then {
    match read_buffer.acctype {
      AccType_ATOMIC   => value = rMem_ATOMIC(read_buffer.address, read_buffer.size),
      AccType_ORDERED  => value = rMem_ATOMIC_ORDERED(read_buffer.address, read_buffer.size),
      _  => { not_implemented("unimplemented memory access"); }
    }
  } else {
    match read_buffer.acctype {
      AccType_NORMAL   => value = rMem_NORMAL (read_buffer.address, read_buffer.size),
      AccType_STREAM   => value = rMem_STREAM (read_buffer.address, read_buffer.size),
      AccType_UNPRIV   => value = rMem_NORMAL (read_buffer.address, read_buffer.size),
      AccType_ORDERED  => value = rMem_ORDERED(read_buffer.address, read_buffer.size),
      AccType_ATOMIC   => assert(false,Some("Reached AccType_ATOMIC: unreachable when address values are known"))
        /*/*old code*/ value = rMem_NORMAL (read_buffer.address, read_buffer.size) /* the second read of 64-bit LDXP */*/
    }
  };

  if BigEndian() then
    value = BigEndianReverse(value);
  value;
}

/** FUNCTION:_Mem[AddressDescriptor desc, integer size, AccType acctype] = bits(8*size) value; */

/* regular store */
/* external */ val wMem_Addr_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, atom('N) /*size*/) -> unit effect {eamem}
/* store-release */
/* external */ val wMem_Addr_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, atom('N) /*size*/) -> unit effect {eamem}
/* store-exclusive */
/* external */ val wMem_Addr_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, atom('N) /*size*/) -> unit effect {eamem}
/* store-exclusive+release */
/* external */ val wMem_Addr_ATOMIC_ORDERED : forall 'N, 'N in {1,2,4,8,16}. (bits(64) /*address*/, atom('N) /*size*/) -> unit effect {eamem}

val wMem_Addr : forall 'N, 'N in {1,2,4,8,16}. (bits(64), atom('N), AccType, boolean) -> unit effect {eamem}
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
/* external */ val wMem_Val_NORMAL : forall 'N, 'N in {1,2,4,8,16}. (atom('N) /*size*/, bits('N*8) /*value*/) -> unit effect {wmv}
/* store-exclusive */
/* external */ val wMem_Val_ATOMIC : forall 'N, 'N in {1,2,4,8,16}. (atom('N) /*size*/, bits('N*8) /*value*/) -> bool effect {wmv}


struct write_buffer_type = {
  acctype : AccType,
  exclusive : bool,
  address : bits(64),
  value : bits(128),
  size : uinteger,
}

let empty_write_buffer = { 
  size = 0;
  /* arbitrary values: */
  acctype = AccType_NORMAL;
  exclusive = false;
  address = 0;
  value = 0;
}

val _wMem : forall 'N, 'N in {1,2,4,8,16}. (write_buffer_type, AddressDescriptor, atom('N), AccType, bool, bits('N*8)) -> write_buffer_type
function _wMem(write_buffer, desc, size, acctype, exclusive, value) = {
  if write_buffer.size == 0 then {
    { acctype = acctype;
      exclusive = exclusive;
      address = (desc.paddress).physicaladdress;
      value : bits(128) = ZeroExtend(value);
      size = size;
    }
  } else {
    assert((write_buffer.acctype == acctype),None);
    assert((write_buffer.exclusive == exclusive), None);
    assert(((write_buffer.address + write_buffer.size) : bits(64) == (desc.paddress).physicaladdress),None);

    { write_buffer with
      value = (ZeroExtend(value @ (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])),
      size = write_buffer.size + size
    }
  }
}

val flush_write_buffer : write_buffer_type -> unit effect {wmv}
function flush_write_buffer(write_buffer) = {
  assert((write_buffer.exclusive == false), None);

  match write_buffer.acctype {
    AccType_NORMAL   => wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    AccType_STREAM   => wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    AccType_UNPRIV   => wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    _  => not_implemented("unrecognised memory access")
  };
}

val flush_write_buffer_exclusive : write_buffer_type -> bool effect {wmv}
function flush_write_buffer_exclusive(write_buffer) = {
  assert((write_buffer.exclusive), None);

  match write_buffer.acctype {
    AccType_ATOMIC   => wMem_Val_ATOMIC(write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    AccType_ORDERED  => wMem_Val_ATOMIC(write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]),
    _  => { not_implemented("unrecognised memory access"); false; }
  };
}

/** FUNCTION:BranchTo(bits(N) target, BranchType branch_type) */

val BranchTo : forall 'N, 'N in {32,64}. BranchType -> unit effect {rreg,wreg}
function BranchTo(target, branch_type) = {
  target' : bits('N) = target; /* Sail does not let you change parameter vector */

  Hint_Branch(branch_type);
  if length(target) == 32 then {
    assert( UsingAArch32(), None );
    _PC = ZeroExtend(target);
  } else {
    assert(( length(target) == 64 & ~(UsingAArch32()) ), None);
    /* Remove the tag bits from tagged target */
    let pstate_el = PSTATE_EL in {
      if pstate_el == EL0 then {
        if target'[55] == 1 & TCR_EL1.TBI1 == 1 then
          target'[63..56] = 0b11111111;
        if target'[55] == 0 & TCR_EL1.TBI0 == 1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL1 then {
        if target'[55] == 1 & TCR_EL1.TBI1 == 1 then
          target'[63..56] = 0b11111111;
        if target'[55] == 0 & TCR_EL1.TBI0 == 1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL2 then {
        if TCR_EL2.TBI == 1 then
          target'[63..56] = 0b00000000;
      }
      else if pstate_el == EL3 then {
        if TCR_EL3.TBI == 1 then
          target'[63..56] = 0b00000000;
      }
      else assert(false,None)
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
val ResetExternalDebugRegisters : boolean -> unit
function unit ResetExternalDebugRegisters (b) = 
  not_implemented_extern("ResetExternalDebugRegisters")
/** FUNCTION:shared/functions/registers/ThisInstrAddr */

val ThisInstrAddr : forall 'N, 'N >= 0. implicit('N) -> bits('N) effect {rreg}
function ThisInstrAddr() = {
  let N = (length(0 : bits('N))) in {
  assert((N == 64 | (N == 32 & UsingAArch32())), None);
  /*return*/ mask(rPC());
}}

/** FUNCTION:// SPSR[] - non-assignment form */

function rSPSR() -> bits(32) = {
  result : bits(32) = 0; /* ARM: uninitialized */
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
    let pstate_el = PSTATE_EL in {
      if      pstate_el == EL1 then result = SPSR_EL1
      else if pstate_el == EL2 then result = SPSR_EL2
      else if pstate_el == EL3 then result = SPSR_EL3
      else Unreachable()
    };
  };

  result;
}

/** FUNCTION:shared/functions/system/ClearEventRegister */
function unit ClearEventRegister () = not_implemented_extern("ClearEventRegister")
/** FUNCTION:boolean ConditionHolds(bits(4) cond) */

val ConditionHolds : bits(4) -> boolean effect {rreg}
function ConditionHolds(_cond) = {
  result : boolean = false; /* ARM: uninitialized */
  /* Evaluate base condition */
  match _cond[3..1] {
    0b000  => result = (PSTATE_Z == 1),                        /* EQ or NE */
    0b001  => result = (PSTATE_C == 1),                        /* CS or CC */
    0b010  => result = (PSTATE_N == 1),                        /* MI or PL */
    0b011  => result = (PSTATE_V == 1),                        /* VS or VC */
    0b100  => result = (PSTATE_C == 1 & PSTATE_Z == 0),        /* HI or LS */
    0b101  => result = (PSTATE_N == PSTATE_V),                 /* GE or LT */
    0b110  => result = (PSTATE_N == PSTATE_V & PSTATE_Z == 0), /* GT or LE */
    0b111  => result = true                                    /* AL */
  };

  /* Condition flag values in the set '111x' indicate always true */
  /* Otherwise, invert condition if necessary. */
  if _cond[0] == 1 & _cond != 0b1111 then
    result = ~(result);

  result;
}

/** ENUMERATE:shared/functions/system/EL0 */
/** FUNCTION:boolean ELUsingAArch32(bits(2) el) */

function ELUsingAArch32(el : bits(2)) -> boolean =
    false /* ARM: ELStateUsingAArch32(el, IsSecureBelowEL3()) */ /* FIXME: implement */

/** FUNCTION:shared/functions/system/EventRegisterSet */
function unit EventRegisterSet () = not_implemented_extern("EventRegisterSet")
/** FUNCTION:shared/functions/system/EventRegistered */
function boolean EventRegistered () = not_implemented_extern("EventRegistered")
/** FUNCTION:shared/functions/system/HaveAArch32EL */

function boolean HaveAArch32EL(el : bits(2)) = {
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

function boolean HaveAnyAArch32() =
{
  IMPLEMENTATION_DEFINED.HaveAnyAArch32
}

/** FUNCTION:boolean HaveEL(bits(2) el) */

function boolean HaveEL(el : bits(2)) = {
  if el == EL1 | el == EL0 then
    true /*EL1 and EL0 must exist*/
  else {

  if      el == EL2 then IMPLEMENTATION_DEFINED.HaveEL2
  else if el == EL3 then IMPLEMENTATION_DEFINED.HaveEL3
  else {assert (false,None); false};
  };
}

/** FUNCTION:boolean HighestELUsingAArch32() */

function boolean HighestELUsingAArch32() =
{
  if ~(HaveAnyAArch32()) then false else
  IMPLEMENTATION_DEFINED.HighestELUsingAArch32; /* e.g. CFG32SIGNAL == HIGH */
}

/** FUNCTION:shared/functions/system/Hint_Yield */

function unit Hint_Yield() = ()

/** FUNCTION:shared/functions/system/InstructionSynchronizationBarrier */
/* external */ val InstructionSynchronizationBarrier : unit -> unit effect {barr}
/** FUNCTION:shared/functions/system/InterruptPending */

function boolean InterruptPending () = not_implemented_extern("InterruptPending")

/** FUNCTION:boolean IsSecure() */

function boolean IsSecure() =
{
  /*Return TRUE if current Exception level is in Secure state.*/
  if HaveEL(EL3) & ~(UsingAArch32()) & PSTATE_EL == EL3 then
    true
  else if HaveEL(EL3) & UsingAArch32() & PSTATE_M == M32_Monitor then
    true
  else
    IsSecureBelowEL3();
}

/** FUNCTION:boolean IsSecureBelowEL3() */

function boolean IsSecureBelowEL3() = {
  if HaveEL(EL3) then
    ((SCR_GEN()).NS == 0)
  else if HaveEL(EL2) then
    false
  else
    /*TRUE if processor is Secure or FALSE if Non-secure;*/
    IMPLEMENTATION_DEFINED.IsSecureBelowEL3;
}

/** ENUMERATE:shared/functions/system/Mode_Bits */
/** FUNCTION:shared/functions/system/SCR_GEN */

function SCRType SCR_GEN() = {
  /*AArch32 secure & AArch64 EL3 registers are not architecturally mapped*/
  assert (HaveEL(EL3),None);

  if HighestELUsingAArch32() then
    SCR
  else
    SCR_EL3;
}

/** FUNCTION:shared/functions/system/SendEvent */

function unit SendEvent() =
{
  ()
  /* TODO: ??? */
}

/** FUNCTION:shared/functions/system/Unreachable */

function unit Unreachable() =
{
    assert (false,Some("Unreachable reached"));
}

/** FUNCTION:shared/functions/system/UsingAArch32 */

function boolean UsingAArch32() =
{
  false;
  /* ARM: uncomment when implementing aarch32
  boolean aarch32 = (PSTATE.nRW == '1');
  if !HaveAnyAArch32() then assert !aarch32;
  if HighestELUsingAArch32() then assert aarch32;
  return aarch32;*/
}

/** FUNCTION:shared/functions/system/WaitForEvent */
function unit WaitForEvent () = not_implemented_extern("WaitForEvent")
/** FUNCTION:shared/functions/system/WaitForInterrupt */
function unit WaitForInterrupt () = not_implemented_extern("WaitForInterrupt")
/** FUNCTION:shared/translation/translation/PAMax */

function uinteger PAMax() =
{
  pa_size : uinteger = 0;
  match ID_AA64MMFR0_EL1.PARange {
    0b0000  => pa_size = 32,
    0b0001  => pa_size = 36,
    0b0010  => pa_size = 40,
    0b0011  => pa_size = 42,
    0b0100  => pa_size = 44,
    0b0101  => pa_size = 48,
    _  => Unreachable()
  };

  /*return*/ pa_size;
}

/** FUNCTION:shared/translation/translation/S1TranslationRegime */

val S1TranslationRegime : unit -> bits(2) effect {rreg}
function S1TranslationRegime () = {
  if PSTATE_EL != EL0 then
    PSTATE_EL
  else if IsSecure() & HaveEL(EL3) & ELUsingAArch32(EL3) then
    EL3
  else
    EL1
}

