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

(** FUNCTION:shared/debug/DoubleLockStatus/DoubleLockStatus *)

function boolean DoubleLockStatus() =
{
  if ELUsingAArch32(EL1) then
    (DBGOSDLR.DLK == 1 & DBGPRCR.CORENPDRQ == 0 & ~(Halted()))
  else
    (OSDLR_EL1.DLK == 1 & DBGPRCR_EL1.CORENPDRQ == 0 & ~(Halted()));
}

(** FUNCTION:shared/debug/authentication/Debug_authentication *)

(* TODO: these are external signals *)

typedef signalValue =
  enumerate {LOw; HIGH}

function signalValue signalDBGEN () = not_implemented_extern("signalDBGEN")
function signalValue signelNIDEN () = not_implemented_extern("signalNIDEN")
function signalValue signalSPIDEN () = not_implemented_extern("signalSPIDEN")
function signalValue signalDPNIDEN () = not_implemented_extern("signalSPNIDEN")

(** FUNCTION:shared/debug/authentication/ExternalInvasiveDebugEnabled *)

function boolean ExternalInvasiveDebugEnabled() =
{
  (* In the recommended interface, ExternalInvasiveDebugEnabled returns the state of the DBGEN *)
  (* signal. *)
  signalDBGEN() == HIGH;
}

(** FUNCTION:shared/debug/authentication/ExternalSecureInvasiveDebugEnabled *)

function boolean ExternalSecureInvasiveDebugEnabled() =
{
  (* In the recommended interface, ExternalSecureInvasiveDebugEnabled returns the state of the *)
  (* (DBGEN AND SPIDEN) signal. *)
  (* CoreSight allows asserting SPIDEN without also asserting DBGEN, but this is not recommended. *)
  if ~(HaveEL(EL3)) & ~(IsSecure()) then false
  else {
  (ExternalInvasiveDebugEnabled() & signalSPIDEN() == HIGH);
}}

(** FUNCTION:shared/debug/halting/DCPSInstruction *)

function unit DCPSInstruction((bit[2]) target_el) =
{
  not_implemented("DCPSInstruction");
}

(** FUNCTION:shared/debug/halting/DRPSInstruction *)

function unit DRPSInstruction() =
{
  not_implemented("DRPSInstruction");
}

(** TYPE:shared/debug/halting/DebugHalt *)

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

(** FUNCTION:shared/debug/halting/Halt *)

function unit Halt((bit[6]) reason) =
{
  not_implemented("Halt");
}

(** FUNCTION:shared/debug/halting/Halted *)

function boolean Halted() =
{
  ~(EDSCR.STATUS == 0b000001 | EDSCR.STATUS == 0b000010); (* Halted *)
}

(** FUNCTION:shared/debug/halting/HaltingAllowed *)

function boolean HaltingAllowed() =
{
  if Halted() | DoubleLockStatus() then
    false
  else if IsSecure() then
    ExternalSecureInvasiveDebugEnabled()
  else
    ExternalInvasiveDebugEnabled();
}

(** FUNCTION:shared/exceptions/traps/ReservedValue *)

function unit ReservedValue() =
{
  (* ARM: uncomment when adding aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException()
  else*)
    AArch64_UndefinedFault();
}

(** FUNCTION:shared/exceptions/traps/UnallocatedEncoding *)

function unit UnallocatedEncoding() =
{
  (* If the unallocated encoding is an AArch32 CP10 or CP11 instruction, FPEXC.DEX must be written *)
  (* to zero. This is omitted from this code. *)
  (* ARM: uncomment whenimplementing aarch32
  if UsingAArch32() && !AArch32.GeneralExceptionsToAArch64() then
    AArch32.TakeUndefInstrException();
  else*)
    AArch64_UndefinedFault();
}

(** FUNCTION:shared/functions/aborts/IsFault *)

function boolean IsFault((AddressDescriptor) addrdesc) =
{
    (addrdesc.fault).type != Fault_None;
}

(** FUNCTION:shared/functions/common/ASR *)

function forall Nat 'N. bit['N] ASR((bit['N]) x, (uinteger) shift) =
{
  (*assert shift >= 0;*)
  (bit['N]) result := 0;
  if shift == 0 then
    result := x
  else
    let (result', _) = (ASR_C(x, shift)) in { result := result' };
  result;
}

(** FUNCTION:shared/functions/common/ASR_C *)

function forall Nat 'N, Nat 'S, 'S >= 1. (bit['N], bit) ASR_C((bit['N]) x, ([:'S:]) shift) =
{
  (*assert shift > 0;*)
  (bit['S+'N]) extended_x := SignExtend(x);
  (bit['N]) result := extended_x[(shift + length(x) - 1)..shift];
  (bit) carry_out := extended_x[shift - 1];
  (result, carry_out);
}

(** FUNCTION:integer Align(integer x, integer y) *)

function uinteger Align'((uinteger) x, (uinteger) y) =
    y * (x quot y)

(** FUNCTION:bits(N) Align(bits(N) x, integer y) *)

function forall Nat 'N. bit['N] Align((bit['N]) x, (uinteger) y) =
  (bit['N]) (Align'(UInt(x), y))

(** FUNCTION:integer CountLeadingSignBits(bits(N) x) *)

function forall Nat 'N. [|'N|] CountLeadingSignBits((bit['N]) x) =
  CountLeadingZeroBits(x[(length(x) - 1)..1] ^ x[(length(x) - 2)..0])

(** FUNCTION:integer CountLeadingZeroBits(bits(N) x) *)

function forall Nat 'N. [|'N|] CountLeadingZeroBits((bit['N]) x) =
  switch HighestSetBit(x) {
    case None -> length(x)
    case (Some(n)) -> length(x) - 1 - n
  }
(** FUNCTION:bits(N) Extend(bits(M) x, integer N, boolean unsigned) *)

val forall Nat 'N, Nat 'M, 'M <= 'N. (implicit<'N>,bit['M],bit) -> bit['N] effect pure Extend
function forall Nat 'N, Nat 'M. bit['N] Extend (x, unsigned) =
  if unsigned then ZeroExtend(x) else SignExtend(x)

(** FUNCTION:integer HighestSetBit(bits(N) x) *)

function forall Nat 'N. option<[|0:('N + -1)|]> HighestSetBit((bit['N]) x) = {
  let N = (length(x)) in {
  ([|('N + -1)|]) result := 0;
  (bool) break := false;
  foreach (i from (N - 1) downto 0)
    if ~(break) & x[i] == 1 then {
      result := i;
      break := true;
    };

  if break then Some(result) else None;
}}

(** FUNCTION:integer Int(bits(N) x, boolean unsigned) *)

function forall Nat 'N. integer Int((bit['N]) x, (boolean) unsigned) = {
  result := if unsigned then UInt(x) else SInt(x);
  result;
}

(** FUNCTION:boolean IsZero(bits(N) x) *)

function forall Nat 'N. boolean IsZero((bit['N]) x) = x == 0 (* ARM: Zeros(N) *)

(** FUNCTION:bit IsZeroBit(bits(N) x) *)

function forall Nat 'N. bit IsZeroBit((bit['N]) x) = if IsZero(x) then 1 else 0

(** FUNCTION:shared/functions/common/LSL *)

function forall Nat 'N. bit['N] LSL((bit['N]) x, (uinteger) shift) =
{
  (*assert shift >= 0;*)
  (bit['N]) result := 0;
  if shift == 0 then
    result := x
  else
    let (result', _) = (LSL_C(x, shift)) in { result := result' };
  result;
}

(** FUNCTION:shared/functions/common/LSL_C *)

function forall Nat 'N, Nat 'S, 'S >= 1. (bit['N], bit) LSL_C((bit['N]) x, ([:'S:]) shift) =
{
  (*assert shift > 0;*)
  (bit['N + 'S]) extended_x := x : (bit['S]) (Zeros());
  (bit['N]) result := (bit['N]) (mask(extended_x));
  (bit) carry_out := extended_x[length(x)];
  (result, carry_out);
}

(** FUNCTION:shared/functions/common/LSR *)

function forall Nat 'N. bit['N] LSR((bit['N]) x, (uinteger) shift) =
{
  (*assert shift >= 0;*)
  (bit['N]) result := 0;
  if shift == 0 then
    result := x
  else
    let (result', _) = (LSR_C(x, shift)) in { result := result' };
  result;
}

(** FUNCTION:shared/functions/common/LSR_C *)

function forall Nat 'N, Nat 'S, 'S >= 1. (bit['N], bit) LSR_C((bit['N]) x, ([:'S:]) shift) =
{
  (*assert shift > 0;*)
  (bit['N + 'S]) extended_x := ZeroExtend(x);
  (bit['N]) result := extended_x[(shift + length(x) - 1)..shift];
  (bit) carry_out := extended_x[shift - 1];
  (result, carry_out);
}

(** FUNCTION:integer Min(integer a, integer b) *)

function integer Min((integer) a, (integer) b) =
{
  if a <= b then a else b;
}

function uinteger uMin((uinteger) a, (uinteger) b) =
{
  if a <= b then a else b;
}

(** FUNCTION:bits(N) NOT(bits(N) x); *)

function forall Nat 'N. bit['N] NOT((bit['N]) x) = ~(x)
function bit NOT'((bit) x) = ~(x)

(** FUNCTION:shared/functions/common/Ones *)

function forall Nat 'N. bit['N] Ones() = Replicate([1])

(** FUNCTION:shared/functions/common/ROR *)

function forall Nat 'N. bit['N] ROR((bit['N]) x, (uinteger) shift) =
{
  (*assert shift >= 0;*)
  (bit['N]) result := 0;
  if shift == 0 then
    result := x
  else
    let (result', _) = (ROR_C(x, shift)) in { result := result' };
  result;
}

(** FUNCTION:shared/functions/common/ROR_C *)

function forall Nat 'N, Nat 'S, 'S >= 1, 'S <= -1. (bit['N], bit) ROR_C((bit['N]) x, ([:'S:]) shift) =
{
  let N = (length(x)) in {
  (*assert shift != 0;*)
  (nat) m := shift mod N;
  (bit['N]) result := (LSR(x,m) | LSL(x,N - m));
  (bit) carry_out := result[N - 1];
  (result, carry_out);
}}

(** FUNCTION:shared/functions/common/Replicate *)

function forall Nat 'N, Nat 'M. bit['N] Replicate((bit['M]) x) = {
  let (N,M) = (length((bit['N]) 0), length((bit['M]) 0)) in {
  assert((N mod M == 0),None);

  (bit['N]) result := 0;
  zeros := (bit['N-'M]) (Zeros());
  foreach (i from M to N by M) result := ((result << M) | zeros:x);

  result;
}}

(** FUNCTION:integer SInt(bits(N) x) *)

(*function forall Nat 'N, Nat 'M, Nat 'K, 'M = 'N + -1, 'K = 2**'M. [|'K * -1:'K + -1|] SInt((bit['N]) x) =*)
function forall Nat 'N, Nat 'M. [:'M:] SInt((bit['N]) x) =
{ signed(x)
  (*let N = (length((bit['N]) 0)) in {
  (integer) result := (nat) x;
  if x[N - 1] == 1 then result := result - (2 ** N);
  result;
}*)}


(** FUNCTION:bits(N) SignExtend(bits(M) x, integer N) *)

function forall Nat 'N, Nat 'M. bit['N] SignExtend ((bit['M]) ([h]:remainder as x)) =
  ((bit[('N - 'M)]) (Replicate([h]))) : x

(** FUNCTION:integer UInt(bits(N) x) *)

(* function forall Nat 'N, Nat 'M, 'M = 2**'N. [|'M + -1|] UInt((bit['N]) x) = ([|'M + -1|]) x *)
function forall Nat 'N, Nat 'M. [:'M:] UInt((bit['N]) x) = unsigned(x)

(** FUNCTION:bits(N) ZeroExtend(bits(M) x, integer N) *)

function forall Nat 'M, Nat 'N. bit['N] ZeroExtend ((bit['M]) x) =
  ((bit[('N + 'M * -1)]) (Zeros())) : x

(** FUNCTION:shared/functions/common/Zeros *)

function forall Nat 'N. bit['N] Zeros() = (bit['N]) 0 (* ARM: Zeros(N) *)

(** FUNCTION:bits(N) BitReverse(bits(N) data) *)

function forall Nat 'N. bit['N] BitReverse((bit['N]) data) = {
  let N = (length(data)) in {
  (bit['N]) result := 0; (* ARM: uninitialized *)
  foreach (i from 0 to (N - 1))
    result[N - i - 1] := data[i];
  result;
}}

(** FUNCTION:shared/functions/crc/HaveCRCExt *)

(* TODO: this should not be hardcoded *)
function (boolean) HaveCRCExt() = IMPLEMENTATION_DEFINED.HaveCRCExt

(** FUNCTION:bits(32) Poly32Mod2(bits(N) data, bits(32) poly) *)

function forall Nat 'N. bit[32] Poly32Mod2((bit['N]) data, (bit[32]) poly) = {
  (bit['N]) result := data;
  let N = (length(data)) in {
  assert((N > 32 ),None);
  (bit['N]) data' := data;
  (bit['N - 32]) zeros := Zeros();
  foreach (i from (N - 1) downto 32) {
    if data'[i] == 1 then
      data'[(i - 1)..0] := data'[(i - 1)..0] ^ (poly:zeros[(i - 33)..0]);
  };
  data'[31..0];
}}

(** FUNCTION:shared/functions/exclusive/ClearExclusiveByAddress *)

function unit effect pure ClearExclusiveByAddress((FullAddress) paddress, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

(** FUNCTION:shared/functions/exclusive/ClearExclusiveLocal *)

function unit effect pure ClearExclusiveLocal((int) processorid) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

(** FUNCTION:shared/functions/exclusive/ExclusiveMonitorsStatus *)

function bit effect pure ExclusiveMonitorsStatus() =
{
  info("The model does not implement the exclusive monitors explicitly.");
  not_implemented("ExclusiveMonitorsStatus should not be called");
  0;
}

(** FUNCTION:shared/functions/exclusive/IsExclusiveGlobal *)

function boolean effect pure IsExclusiveGlobal((FullAddress) paddress, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

(** FUNCTION:shared/functions/exclusive/IsExclusiveLocal *)

function boolean effect pure IsExclusiveLocal((FullAddress) paddress, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
  true;
}

(** FUNCTION:shared/functions/exclusive/MarkExclusiveGlobal *)

function unit effect pure MarkExclusiveGlobal((FullAddress) paddress, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

(** FUNCTION:shared/functions/exclusive/MarkExclusiveLocal *)

function unit effect pure MarkExclusiveLocal((FullAddress) paddress, (integer) processorid, (uinteger) size) =
{
  info("The model does not implement the exclusive monitors explicitly.");
}

(** FUNCTION:shared/functions/exclusive/ProcessorID *)

(* FIXME: return the real number? *)
function integer ProcessorID() = {0}

(** FUNCTION:(bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in) *)

function forall Nat 'N. (bit['N],bit[4]) AddWithCarry ((bit['N]) x, (bit['N]) y, (bit) carry_in) = {
  (uinteger) unsigned_sum := UInt(x) + UInt(y) + UInt([carry_in]);
  (integer) signed_sum := SInt(x) + SInt(y) + UInt([carry_in]);
  (bit['N]) result := (bit['N]) unsigned_sum; (* same value as signed_sum<N-1:0> *)
  (bit) n := result[(length(result)) - 1];
  (bit) z := if IsZero(result) then 1 else 0;
  (bit) c := if UInt(result) == unsigned_sum then 0 else 1;
  (bit) v := if SInt(result) == signed_sum then 0 else 1;
  (result,[n]:[z]:[c]:[v])
}

(** TYPE:shared/functions/memory/AddressDescriptor *)
(** FUNCTION:boolean BigEndian() *)

function boolean effect {rreg} BigEndian() = {
    (boolean) bigend := 0; (* ARM: uninitialized *)
    if UsingAArch32() then
        bigend := (PSTATE_E != 0)
    else if PSTATE_EL == EL0 then
        bigend := (SCTLR_EL1.E0E != 0)
    else
        bigend := ((SCTLR'()).EE != 0);
    bigend;
}

(** FUNCTION:shared/functions/memory/BigEndianReverse *)
val forall Nat 'W, 'W IN {8,16,32,64,128}. bit['W] -> bit['W] effect pure BigEndianReverse
function rec forall Nat 'W, 'W IN {8, 16, 32, 64, 128}. bit['W] BigEndianReverse ((bit['W]) value) =
{
    (uinteger) width := length(value);
    (uinteger) half := width quot 2;
    if width == 8 then (*return*) value
    else (*return*) BigEndianReverse(value[(half - 1)..0]) : BigEndianReverse(value[(width - 1)..half]);
}

(** FUNCTION:shared/functions/memory/DataMemoryBarrier *)

val extern unit -> unit effect {barr} DataMemoryBarrier_Reads
val extern unit -> unit effect {barr} DataMemoryBarrier_Writes
val extern unit -> unit effect {barr} DataMemoryBarrier_All

function unit effect {barr} DataMemoryBarrier((MBReqDomain) domain, (MBReqTypes) types) =
{
  if domain != MBReqDomain_FullSystem & domain != MBReqDomain_InnerShareable then
    not_implemented("DataMemoryBarrier: not MBReqDomain_FullSystem or _InnerShareable");

  switch types {
    case MBReqTypes_Reads  -> DataMemoryBarrier_Reads()
    case MBReqTypes_Writes -> DataMemoryBarrier_Writes()
    case MBReqTypes_All    -> DataMemoryBarrier_All()
  };
}

(** FUNCTION:shared/functions/memory/DataSynchronizationBarrier *)

val extern unit -> unit effect {barr} DataSynchronizationBarrier_Reads
val extern unit -> unit effect {barr} DataSynchronizationBarrier_Writes
val extern unit -> unit effect {barr} DataSynchronizationBarrier_All

function unit effect {barr} DataSynchronizationBarrier((MBReqDomain) domain, (MBReqTypes) types) =
{
  if domain != MBReqDomain_FullSystem then
    not_implemented("DataSynchronizationBarrier: not MBReqDomain_FullSystem");

  switch types {
    case MBReqTypes_Reads  -> DataSynchronizationBarrier_Reads()
    case MBReqTypes_Writes -> DataSynchronizationBarrier_Writes()
    case MBReqTypes_All    -> DataSynchronizationBarrier_All()
  };
}

(** ENUMERATE:shared/functions/memory/DeviceType *)
(** ENUMERATE:shared/functions/memory/DeviceType *)
(** TYPE:shared/functions/memory/FaultRecord *)
(** TYPE:shared/functions/memory/FullAddress *)
(** FUNCTION:shared/functions/memory/Hint_Prefetch *)
val (bit[64],PrefetchHint,integer,boolean) -> unit effect pure Hint_Prefetch
function unit effect pure Hint_Prefetch(addr,hint,target,stream) = ()
(** ENUMERATE:shared/functions/memory/MBReqDomain *)
(** ENUMERATE:shared/functions/memory/MBReqTypes *)
(** TYPE:shared/functions/memory/MemAttrHints *)
(** ENUMERATE:shared/functions/memory/MemType *)
(** TYPE:shared/functions/memory/MemoryAttributes *)
(** ENUMERATE:shared/functions/memory/PrefetchHint *)
(** FUNCTION:shared/functions/memory/_Mem *)

(* regular load *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*),[:'N:] (*size*)) -> bit['N*8] effect {rmem} rMem_NORMAL
(* non-temporal load (LDNP), see ARM ARM for special exception to normal memory ordering rules *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*),[:'N:] (*size*)) -> bit['N*8] effect {rmem} rMem_STREAM
(* load-acquire *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*),[:'N:] (*size*)) -> bit['N*8] effect {rmem} rMem_ORDERED
(* load-exclusive *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*),[:'N:] (*size*)) -> bit['N*8] effect {rmem} rMem_ATOMIC
(* load-exclusive+acquire *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*),[:'N:] (*size*)) -> bit['N*8] effect {rmem} rMem_ATOMIC_ORDERED

typedef read_buffer_type = const struct
{
  AccType acctype;
  (bool) exclusive;
  (bit[64]) address;
  (uinteger) size;
}

let empty_read_buffer =
{ size = 0;
  (* arbitrary values: *)
  acctype = AccType_NORMAL;
  exclusive = false;
  address = 0;
}

function forall Nat 'N, 'N IN {1,2,4,8,16}. read_buffer_type effect pure _rMem((read_buffer_type) read_buffer, (AddressDescriptor) desc, ([:'N:]) size, (AccType) acctype, (bool) exclusive) =
{
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
    assert(((bit[64]) (read_buffer.address + read_buffer.size) == (desc.paddress).physicaladdress), None);

    {read_buffer with size = read_buffer.size + size}
  }
}

function forall Nat 'N, 'N IN {1,2,4,8,16}. bit['N*8] effect {rmem} flush_read_buffer((read_buffer_type) read_buffer, ([:'N:]) size) =
{
  assert((read_buffer.size == size), None);

  (bit['N*8]) value := 0;

  if read_buffer.exclusive then {
    switch read_buffer.acctype {
      case AccType_ATOMIC  -> value := rMem_ATOMIC(read_buffer.address, read_buffer.size)
      case AccType_ORDERED -> value := rMem_ATOMIC_ORDERED(read_buffer.address, read_buffer.size)
      case _ -> { not_implemented("unimplemented memory access"); }
    }
  } else {
    switch read_buffer.acctype {
      case AccType_NORMAL  -> value := rMem_NORMAL (read_buffer.address, read_buffer.size)
      case AccType_STREAM  -> value := rMem_STREAM (read_buffer.address, read_buffer.size)
      case AccType_UNPRIV  -> value := rMem_NORMAL (read_buffer.address, read_buffer.size)
      case AccType_ORDERED -> value := rMem_ORDERED(read_buffer.address, read_buffer.size)
      case AccType_ATOMIC  -> assert(false,Some("Reached AccType_ATOMIC: unreachable when address values are known"))
        (*(*old code*) value := rMem_NORMAL (read_buffer.address, read_buffer.size) (* the second read of 64-bit LDXP *)*)
    }
  };

  if BigEndian() then
    value := BigEndianReverse(value);
  value;
}

(** FUNCTION:_Mem[AddressDescriptor desc, integer size, AccType acctype] = bits(8*size) value; *)

(* regular store *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} wMem_Addr_NORMAL
(* store-release *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} wMem_Addr_ORDERED
(* store-exclusive *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} wMem_Addr_ATOMIC
(* store-exclusive+release *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. (bit[64] (*address*), [:'N:] (*size*)) -> unit effect {eamem} wMem_Addr_ATOMIC_ORDERED

function forall Nat 'N, 'N IN {1,2,4,8,16}. unit effect {eamem} wMem_Addr((bit[64]) address, ([:'N:]) size, (AccType) acctype, (boolean) excl) =
{
  switch (excl, acctype) {
    case (false, AccType_NORMAL)  -> wMem_Addr_NORMAL(address, size)
    case (false, AccType_STREAM)  -> wMem_Addr_NORMAL(address, size)
    case (false, AccType_UNPRIV)  -> wMem_Addr_NORMAL(address, size)
    case (false, AccType_ORDERED) -> wMem_Addr_ORDERED(address, size)
    case (true, AccType_ATOMIC)   -> wMem_Addr_ATOMIC(address, size)
    case (true, AccType_ORDERED)  -> wMem_Addr_ATOMIC_ORDERED(address, size)
    case _ -> not_implemented("unrecognised memory access")
  };
}


(* regular store *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. ([:'N:] (*size*), bit['N*8] (*value*)) -> unit effect {wmv} wMem_Val_NORMAL
(* store-exclusive *)
val extern forall Nat 'N, 'N IN {1,2,4,8,16}. ([:'N:] (*size*), bit['N*8] (*value*)) -> bool effect {wmv} wMem_Val_ATOMIC


typedef write_buffer_type = const struct
{
  AccType acctype;
  (bool) exclusive;
  (bit[64]) address;
  (bit[128]) value;
  (uinteger) size;
}

let empty_write_buffer =
{ size = 0;
  (* arbitrary values: *)
  acctype = AccType_NORMAL;
  exclusive = false;
  address = 0;
  value = 0;
}

function forall Nat 'N, 'N IN {1,2,4,8,16}. write_buffer_type effect pure _wMem((write_buffer_type) write_buffer, (AddressDescriptor) desc, ([:'N:]) size, (AccType) acctype, (bool) exclusive, (bit['N*8]) value) =
{
  if write_buffer.size == 0 then {
    { acctype = acctype;
      exclusive = exclusive;
      address = (desc.paddress).physicaladdress;
      value = (bit[128]) (ZeroExtend(value));
      size = size;
    }
  } else {
    assert((write_buffer.acctype == acctype),None);
    assert((write_buffer.exclusive == exclusive), None);
    assert(((bit[64]) (write_buffer.address + write_buffer.size) == (desc.paddress).physicaladdress),None);

    { write_buffer with
      value = (bit[128]) (ZeroExtend(value : (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0]));
      size = write_buffer.size + size;
    }
  }
}

function unit effect {wmv} flush_write_buffer((write_buffer_type) write_buffer) =
{
  assert((write_buffer.exclusive == false), None);

  switch write_buffer.acctype {
    case AccType_NORMAL  -> wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case AccType_STREAM  -> wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case AccType_UNPRIV  -> wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case AccType_ORDERED -> wMem_Val_NORMAL (write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case _ -> not_implemented("unrecognised memory access")
  };
}

function bool effect {wmv} flush_write_buffer_exclusive((write_buffer_type) write_buffer) =
{
  assert((write_buffer.exclusive), None);

  switch write_buffer.acctype {
    case AccType_ATOMIC  -> wMem_Val_ATOMIC(write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case AccType_ORDERED -> wMem_Val_ATOMIC(write_buffer.size, (write_buffer.value)[((write_buffer.size * 8) - 1) .. 0])
    case _ -> { not_implemented("unrecognised memory access"); false; }
  };
}

(** FUNCTION:BranchTo(bits(N) target, BranchType branch_type) *)

function forall Nat 'N, 'N IN {32,64}. unit effect {rreg,wreg} BranchTo((bit['N]) target, (BranchType) branch_type) = {
  (bit['N]) target' := target; (* Sail does not let you change parameter vector *)

  Hint_Branch(branch_type);
  if length(target) == 32 then {
    assert( UsingAArch32(), None );
    _PC := ZeroExtend(target);
  } else {
    assert(( length(target) == 64 & ~(UsingAArch32()) ), None);
    (* Remove the tag bits from tagged target *)
    let pstate_el = PSTATE_EL in {
      if pstate_el == EL0 then {
        if target'[55] == 1 & TCR_EL1.TBI1 == 1 then
          target'[63..56] := 0b11111111;
        if target'[55] == 0 & TCR_EL1.TBI0 == 1 then
          target'[63..56] := 0b00000000;
      }
      else if pstate_el == EL1 then {
        if target'[55] == 1 & TCR_EL1.TBI1 == 1 then
          target'[63..56] := 0b11111111;
        if target'[55] == 0 & TCR_EL1.TBI0 == 1 then
          target'[63..56] := 0b00000000;
      }
      else if pstate_el == EL2 then {
        if TCR_EL2.TBI == 1 then
          target'[63..56] := 0b00000000;
      }
      else if pstate_el == EL3 then {
        if TCR_EL3.TBI == 1 then
          target'[63..56] := 0b00000000;
      }
      else assert(false,None)
    };
    _PC := target';
  };
}

(** ENUMERATE:shared/functions/registers/BranchType *)
(** FUNCTION:shared/functions/registers/Hint_Branch *)

function unit effect pure Hint_Branch((BranchType) hint) =
{
  info("This hint can be used for hardware optimization that has no effect on the model.");
}

(** FUNCTION:shared/functions/registers/ResetExternalDebugRegisters *)
function unit ResetExternalDebugRegisters ((boolean) b) = not_implemented_extern("ResetExternalDebugRegisters")
(** FUNCTION:shared/functions/registers/ThisInstrAddr *)

val forall Nat 'N. implicit<'N> -> bit['N] effect {rreg} ThisInstrAddr
function forall Nat 'N. bit['N] effect {rreg} ThisInstrAddr() =
{
  let N = (length((bit['N]) 0)) in {
  assert((N == 64 | (N == 32 & UsingAArch32())), None);
  (*return*) mask(rPC());
}}

(** FUNCTION:// SPSR[] - non-assignment form *)

function bit[32] rSPSR() =
{
  (bit[32]) result := 0; (* ARM: uninitialized *)
  if UsingAArch32() then {
    not_implemented("rSPSR UsingAArch32");
    (* ARM:
    case PSTATE.M of
      when M32_FIQ       result = SPSR_fiq;
      when M32_IRQ       result = SPSR_irq;
      when M32_Svc       result = SPSR_svc;
      when M32_Monitor   result = SPSR_mon;
      when M32_Abort     result = SPSR_abt;
      when M32_Hyp       result = SPSR_hyp;
      when M32_Undef     result = SPSR_und;
      otherwise          Unreachable();
    *)
  } else {
    let pstate_el = PSTATE_EL in {
      if      pstate_el == EL1 then result := SPSR_EL1
      else if pstate_el == EL2 then result := SPSR_EL2
      else if pstate_el == EL3 then result := SPSR_EL3
      else Unreachable()
    };
  };

  result;
}

(** FUNCTION:shared/functions/system/ClearEventRegister *)
function unit ClearEventRegister () = not_implemented_extern("ClearEventRegister")
(** FUNCTION:boolean ConditionHolds(bits(4) cond) *)

function boolean effect {rreg} ConditionHolds((bit[4]) _cond) =
{
  (boolean) result := false; (* ARM: uninitialized *)
  (* Evaluate base condition *)
  switch _cond[3..1] {
    case 0b000 -> result := (PSTATE_Z == 1)                        (* EQ or NE *)
    case 0b001 -> result := (PSTATE_C == 1)                        (* CS or CC *)
    case 0b010 -> result := (PSTATE_N == 1)                        (* MI or PL *)
    case 0b011 -> result := (PSTATE_V == 1)                        (* VS or VC *)
    case 0b100 -> result := (PSTATE_C == 1 & PSTATE_Z == 0)        (* HI or LS *)
    case 0b101 -> result := (PSTATE_N == PSTATE_V)                 (* GE or LT *)
    case 0b110 -> result := (PSTATE_N == PSTATE_V & PSTATE_Z == 0) (* GT or LE *)
    case 0b111 -> result := true                                   (* AL *)
  };

  (* Condition flag values in the set '111x' indicate always true *)
  (* Otherwise, invert condition if necessary. *)
  if _cond[0] == 1 & _cond != 0b1111 then
    result := ~(result);

  result;
}

(** ENUMERATE:shared/functions/system/EL0 *)
(** FUNCTION:boolean ELUsingAArch32(bits(2) el) *)

function boolean ELUsingAArch32((bit[2]) el) =
    false (* ARM: ELStateUsingAArch32(el, IsSecureBelowEL3()) *) (* FIXME: implement *)

(** FUNCTION:shared/functions/system/EventRegisterSet *)
function unit EventRegisterSet () = not_implemented_extern("EventRegisterSet")
(** FUNCTION:shared/functions/system/EventRegistered *)
function boolean EventRegistered () = not_implemented_extern("EventRegistered")
(** FUNCTION:shared/functions/system/HaveAArch32EL *)

function boolean HaveAArch32EL((bit[2]) el) =
{
  (* Return TRUE if Exception level 'el' supports AArch32 *)
  if ~(HaveEL(el)) then
    false
  else if ~(HaveAnyAArch32()) then
    false                       (* No exception level can use AArch32    *)
  else if HighestELUsingAArch32() then
    true                        (* All exception levels must use AArch32 *)
  else if el == EL0 then
    true                        (* EL0 must support using AArch32        *)
  else

  IMPLEMENTATION_DEFINED.HaveAArch32EL;
}

(** FUNCTION:boolean HaveAnyAArch32() *)

function boolean HaveAnyAArch32() =
{
  IMPLEMENTATION_DEFINED.HaveAnyAArch32
}

(** FUNCTION:boolean HaveEL(bits(2) el) *)

function boolean HaveEL((bit[2]) el) =
{
  if el == EL1 | el == EL0 then
    true (*EL1 and EL0 must exist*)
  else {

  if      el == EL2 then IMPLEMENTATION_DEFINED.HaveEL2
  else if el == EL3 then IMPLEMENTATION_DEFINED.HaveEL3
  else {assert (false,None); false};
  };
}

(** FUNCTION:boolean HighestELUsingAArch32() *)

function boolean HighestELUsingAArch32() =
{
  if ~(HaveAnyAArch32()) then false else
  IMPLEMENTATION_DEFINED.HighestELUsingAArch32; (* e.g. CFG32SIGNAL == HIGH *)
}

(** FUNCTION:shared/functions/system/Hint_Yield *)

function unit Hint_Yield() = ()

(** FUNCTION:shared/functions/system/InstructionSynchronizationBarrier *)
val extern unit -> unit effect {barr} InstructionSynchronizationBarrier
(** FUNCTION:shared/functions/system/InterruptPending *)

function boolean InterruptPending () = not_implemented_extern("InterruptPending")

(** FUNCTION:boolean IsSecure() *)

function boolean IsSecure() =
{
  (*Return TRUE if current Exception level is in Secure state.*)
  if HaveEL(EL3) & ~(UsingAArch32()) & PSTATE_EL == EL3 then
    true
  else if HaveEL(EL3) & UsingAArch32() & PSTATE_M == M32_Monitor then
    true
  else
    IsSecureBelowEL3();
}

(** FUNCTION:boolean IsSecureBelowEL3() *)

function boolean IsSecureBelowEL3() = {
  if HaveEL(EL3) then
    ((SCR_GEN()).NS == 0)
  else if HaveEL(EL2) then
    false
  else
    (*TRUE if processor is Secure or FALSE if Non-secure;*)
    IMPLEMENTATION_DEFINED.IsSecureBelowEL3;
}

(** ENUMERATE:shared/functions/system/Mode_Bits *)
(** FUNCTION:shared/functions/system/SCR_GEN *)

function SCRType SCR_GEN() = {
  (*AArch32 secure & AArch64 EL3 registers are not architecturally mapped*)
  assert (HaveEL(EL3),None);

  if HighestELUsingAArch32() then
    SCR
  else
    SCR_EL3;
}

(** FUNCTION:shared/functions/system/SendEvent *)

function unit SendEvent() =
{
  ()
  (* TODO: ??? *)
}

(** FUNCTION:shared/functions/system/Unreachable *)

function unit Unreachable() =
{
    assert (false,Some("Unreachable reached"));
}

(** FUNCTION:shared/functions/system/UsingAArch32 *)

function boolean UsingAArch32() =
{
  false;
  (* ARM: uncomment when implementing aarch32
  boolean aarch32 = (PSTATE.nRW == '1');
  if !HaveAnyAArch32() then assert !aarch32;
  if HighestELUsingAArch32() then assert aarch32;
  return aarch32;*)
}

(** FUNCTION:shared/functions/system/WaitForEvent *)
function unit WaitForEvent () = not_implemented_extern("WaitForEvent")
(** FUNCTION:shared/functions/system/WaitForInterrupt *)
function unit WaitForInterrupt () = not_implemented_extern("WaitForInterrupt")
(** FUNCTION:shared/translation/translation/PAMax *)

function uinteger PAMax() =
{
  (uinteger) pa_size := 0;
  switch ID_AA64MMFR0_EL1.PARange {
    case 0b0000 -> pa_size := 32
    case 0b0001 -> pa_size := 36
    case 0b0010 -> pa_size := 40
    case 0b0011 -> pa_size := 42
    case 0b0100 -> pa_size := 44
    case 0b0101 -> pa_size := 48
    case _ -> Unreachable()
  };

  (*return*) pa_size;
}

(** FUNCTION:shared/translation/translation/S1TranslationRegime *)

function bit[2] effect {rreg} S1TranslationRegime () =
{
  if PSTATE_EL != EL0 then
    PSTATE_EL
  else if IsSecure() & HaveEL(EL3) & ELUsingAArch32(EL3) then
    EL3
  else
    EL1
}

