(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2016 Robert M. Norton                              *)
(*  Copyright (c) 2015-2016 Kathyrn Gray                                  *)
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

(* mips_prelude.sail: declarations of mips registers, and functions common 
   to mips instructions (e.g. address translation) *)

(* bit vectors have indices decreasing from left i.e. msb is highest index *)
default Order dec

register (bit[64]) PC
register (bit[64]) nextPC

(* CP0 Registers *)

typedef CauseReg = register bits [ 31 : 0 ] {
  31       : BD; (* branch delay *)
  (*30       : Z0;*)
  29 .. 28 : CE; (* for coprocessor enable exception *)
  (*27 .. 24 : Z1;*)
  23       : IV; (* special interrupt vector not supported *)
  22       : WP; (* watchpoint exception occurred *)
  (*21 .. 16 : Z2; *)
  15 .. 8  : IP; (* interrupt pending bits *)
  (*7        : Z3;*)
  6 .. 2   : ExcCode; (* code of last exception *)
  (*1 .. 0   : Z4;*)
}

typedef TLBEntryLoReg = register bits [63 : 0] {
  63      : CapS;
  62      : CapL;
  29 .. 6 : PFN;
  5  .. 3 : C;
  2       : D;
  1       : V;
  0       : G;
}

typedef TLBEntryHiReg = register bits [63 : 0] {
  63 .. 62 : R;
  39 .. 13 : VPN2;
  7  ..  0 : ASID;
}

typedef ContextReg = register bits [63 : 0] {
  63 .. 23 : PTEBase;
  22 .. 4  : BadVPN2;
  (*3  .. 0  : ZR;*)
}

typedef XContextReg = register bits [63 : 0] {
  63 .. 33: PTEBase;
  32 .. 31: R;
  30 ..  4: BadVPN2;
}

let ([:8:]) TLBNumEntries = 8
typedef TLBIndexT = (bit[3])
let (TLBIndexT) TLBIndexMax = 0b111

let MAX_VA = unsigned(0xffffffffff)
let MAX_PA = unsigned(0xfffffffff)

typedef TLBEntry = register bits [116 : 0] {
  116 ..  101: pagemask;
  100 ..  99 : r       ;
  98  ..  72 : vpn2    ;
  71  ..  64 : asid    ;
  63         : g       ;
  62         : valid   ;
  61         : caps1   ;
  60         : capl1   ;
  59  ..  36 : pfn1    ;
  35  ..  33 : c1      ;
  32         : d1      ;
  31         : v1      ;
  30         : caps0   ;
  29         : capl0   ;
  28  ..  5  : pfn0    ;
  4   ..  2  : c0      ;
  1          : d0      ;
  0          : v0      ;
}

register (bit[1])        TLBProbe
register (bit[3])     TLBIndex
register (bit[3])     TLBRandom
register (TLBEntryLoReg) TLBEntryLo0
register (TLBEntryLoReg) TLBEntryLo1
register (ContextReg)    TLBContext
register (bit[16])       TLBPageMask
register (bit[3])     TLBWired
register (TLBEntryHiReg) TLBEntryHi
register (XContextReg)   TLBXContext

register (TLBEntry) TLBEntry00
register (TLBEntry) TLBEntry01
register (TLBEntry) TLBEntry02
register (TLBEntry) TLBEntry03
register (TLBEntry) TLBEntry04
register (TLBEntry) TLBEntry05
register (TLBEntry) TLBEntry06
register (TLBEntry) TLBEntry07

let (vector <0, 8, inc, (TLBEntry)>) TLBEntries = [
TLBEntry00,
TLBEntry01,
TLBEntry02,
TLBEntry03,
TLBEntry04,
TLBEntry05,
TLBEntry06,
TLBEntry07
]

register (bit[32])  CP0Compare
register (CauseReg) CP0Cause
register (bit[64])  CP0EPC
register (bit[64])  CP0ErrorEPC
register (bit[1])   CP0LLBit
register (bit[64])  CP0LLAddr
register (bit[64])  CP0BadVAddr
register (bit[32])  CP0Count
register (bit[32])  CP0Compare
register (bit[32])  CP0HWREna
register (bit[64])  CP0UserLocal

typedef StatusReg = register bits [31:0] {
  31 .. 28        : CU;  (* co-processor enable bits *)
  (* RP/FR/RE/MX/PX not implemented *)
  22              : BEV; (* use boot exception vectors (initialised to one) *)
  (* TS/SR/NMI not implemented *)
  15 .. 8         : IM;  (* Interrupt mask *)
  7               : KX;  (* kernel 64-bit enable *)
  6               : SX;  (* supervisor 64-bit enable *)
  5               : UX;  (* user 64-bit enable *)
  4 .. 3          : KSU; (* Processor mode *)
  2               : ERL; (* error level (should be initialised to one, but BERI is different) *)
  1               : EXL; (* exception level *)
  0               : IE;  (* interrupt enable *)
}
register (StatusReg) CP0Status

(* Implementation registers -- not ISA defined *)
register (bit[1])  branchPending      (* Set by branch instructions to implement branch delay *)
register (bit[1])  inBranchDelay      (* Needs to be set by outside world when in branch delay slot *)
register (bit[64]) delayedPC          (* Set by branch instructions to implement branch delay *)

(* General purpose registers *)

register (bit[64]) GPR00 (* should never be read or written *)
register (bit[64]) GPR01
register (bit[64]) GPR02
register (bit[64]) GPR03
register (bit[64]) GPR04
register (bit[64]) GPR05
register (bit[64]) GPR06
register (bit[64]) GPR07
register (bit[64]) GPR08
register (bit[64]) GPR09
register (bit[64]) GPR10
register (bit[64]) GPR11
register (bit[64]) GPR12
register (bit[64]) GPR13
register (bit[64]) GPR14
register (bit[64]) GPR15
register (bit[64]) GPR16
register (bit[64]) GPR17
register (bit[64]) GPR18
register (bit[64]) GPR19
register (bit[64]) GPR20
register (bit[64]) GPR21
register (bit[64]) GPR22
register (bit[64]) GPR23
register (bit[64]) GPR24
register (bit[64]) GPR25
register (bit[64]) GPR26
register (bit[64]) GPR27
register (bit[64]) GPR28
register (bit[64]) GPR29
register (bit[64]) GPR30
register (bit[64]) GPR31

(* Special registers For MUL/DIV *)
register (bit[64]) HI
register (bit[64]) LO

let (vector <0, 32, inc, (register<(bit[64])>) >) GPR =
  [ GPR00, GPR01, GPR02, GPR03, GPR04, GPR05, GPR06, GPR07, GPR08, GPR09, GPR10,
  GPR11, GPR12, GPR13, GPR14, GPR15, GPR16, GPR17, GPR18, GPR19, GPR20,
  GPR21, GPR22, GPR23, GPR24, GPR25, GPR26, GPR27, GPR28, GPR29, GPR30, GPR31
  ]

(* Check whether a given 64-bit vector is a properly sign extended 32-bit word *)
val bit[64] -> bool effect pure NotWordVal
function bool NotWordVal (word) = 
    (word[31] ^^ 32) != word[63..32]

(* Read numbered GP reg. (r0 is always zero) *)
val bit[5] -> bit[64] effect {rreg} rGPR
function bit[64] rGPR idx = {
         if idx == 0 then 0 else GPR[idx]
}

(* Write numbered GP reg. (writes to r0 ignored) *)
val (bit[5], bit[64]) -> unit effect {wreg} wGPR
function unit wGPR (idx, v) = {
         if idx == 0 then () else GPR[idx] := v
}

val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> unit effect { wmem } MEMw
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr
val extern forall Nat 'n. ( bit[64] , [|'n|] ) -> (bit[8 * 'n]) effect { rmem } MEMr_reserve
val extern forall Nat 'n. ( bit[64] , [|'n|] , bit[8*'n]) -> bool effect { wmem } MEMw_conditional
val extern unit -> unit effect { barr } MEM_sync

typedef Exception = enumerate
{
   Int; TLBMod; TLBL; TLBS; AdEL; AdES; Sys; Bp; ResI; CpU; Ov; Tr; C2E; C2Trap;
   XTLBRefillL; XTLBRefillS; XTLBInvL; XTLBInvS; MCheck
}

(* Return the ISA defined code for an exception condition *)
function (bit[5]) ExceptionCode ((Exception) ex) =
   switch (ex)
   {
      case Int         -> mask(0x00) (* Interrupt *)
      case TLBMod      -> mask(0x01) (* TLB modification exception *)
      case TLBL        -> mask(0x02) (* TLB exception (load or fetch) *)
      case TLBS        -> mask(0x03) (* TLB exception (store) *)
      case AdEL        -> mask(0x04) (* Address error (load or fetch) *)
      case AdES        -> mask(0x05) (* Address error (store) *)
      case Sys         -> mask(0x08) (* Syscall *)
      case Bp          -> mask(0x09) (* Breakpoint *)
      case ResI        -> mask(0x0a) (* Reserved instruction *)
      case CpU         -> mask(0x0b) (* Coprocessor Unusable *)
      case Ov          -> mask(0x0c) (* Arithmetic overflow *)
      case Tr          -> mask(0x0d) (* Trap *)
      case C2E         -> mask(0x12) (* C2E coprocessor 2 exception *)
      case C2Trap      -> mask(0x12) (* C2Trap maps to same exception code, different vector *)
      case XTLBRefillL -> mask(0x02)
      case XTLBRefillS -> mask(0x03)
      case XTLBInvL    -> mask(0x02)
      case XTLBInvS    -> mask(0x03)
      case MCheck      -> mask(0x18)
   }


val Exception -> unit effect {rreg, wreg} SignalException

function unit SignalExceptionMIPS ((Exception) ex) = 
  {
    (* Only update EPC and BD if not already in EXL mode *)
    if (~ (CP0Status.EXL)) then 
      {
        if (inBranchDelay[0]) then
          {
            CP0EPC := PC - 4;
            CP0Cause.BD := 1;
          }
        else
          {
            CP0EPC := PC;
            CP0Cause.BD := 0;
          }
      };

      (* choose an exception vector to branch to. Some are not supported 
         e.g. Reset *)
      vectorOffset := 
        if (CP0Status.EXL) then
          0x180 (* Always use common vector if in exception mode already *)
        else if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) then 
          0x080
        else if (ex == C2Trap) then
          0x280 (* Special vector for CHERI traps *)
        else
          0x180; (* Common vector *)
      (bit[64]) vectorBase  := if CP0Status.BEV then
                   0xFFFFFFFFBFC00200
                else
                   0xFFFFFFFF80000000;
      nextPC := vectorBase + EXTS(vectorOffset);
      CP0Cause.ExcCode      := ExceptionCode(ex);
      CP0Status.EXL         := 1;
  }

function unit SignalExceptionBadAddr((Exception) ex, (bit[64]) badAddr) =
  {
    CP0BadVAddr := badAddr;
    SignalException(ex);
  }

function unit SignalExceptionTLB((Exception) ex, (bit[64]) badAddr) = {
  CP0BadVAddr := badAddr;
  (TLBContext.BadVPN2) := (badAddr[31..13]);
  (TLBXContext.BadVPN2):= (badAddr[39..13]);
  (TLBXContext.R)      := (badAddr[63..62]);
  (TLBEntryHi.R)       := (badAddr[63..62]);
  (TLBEntryHi.VPN2)    := (badAddr[39..13]);
  SignalException(ex);
}

typedef MemAccessType = enumerate {Instruction; LoadData; StoreData}
typedef AccessLevel   = enumerate {User; Supervisor; Kernel} 

function AccessLevel getAccessLevel() =
  if ((CP0Status.EXL) | (CP0Status.ERL)) then
    Kernel
  else switch (CP0Status.KSU)
    {
      case 0b00 -> Kernel
      case 0b01 -> Supervisor
      case 0b10 -> User
      case _    -> User (* behaviour undefined, assume user *)
    }

function unit checkCP0Access () =
  {
    let accessLevel = getAccessLevel() in
    if ((accessLevel != Kernel) & (~((CP0Status.CU)[28]))) then
      {
        (CP0Cause.CE) := 0b00;
        exit (SignalException(CpU));
      }
  }

function unit incrementCP0Count() = {
  TLBRandom := (if (unsigned(TLBRandom) == unsigned(TLBWired))
    then (TLBIndexMax) else (TLBRandom - 1));

  CP0Count := (CP0Count + 1);
  if (unsigned(CP0Count) == unsigned(CP0Compare)) then {
    (CP0Cause[15]) := bitone; (* XXX indexing IP field here doesn't seem to work  *)
  };

  let (bit[8]) ims = CP0Status.IM in
  let (bit[8]) ips = CP0Cause.IP in
  let ie           = CP0Status.IE in
  let exl          = CP0Status.EXL in
  let erl          = CP0Status.ERL in
  if ((~(exl)) & (~(erl)) & ie & ((ips & ims) != 0x00)) then
    exit (SignalException(Int));
}

function bool tlbEntryMatch(r, vpn2, asid, (TLBEntry) entry) = 
      let entryValid = entry.valid in
      let entryR     = entry.r in
      let entryMask  = entry.pagemask in
      let entryVPN   = entry.vpn2 in
      let entryASID  = entry.asid in
      let entryG     = entry.g in
      (entryValid &
       (r == entryR) & 
       ((vpn2 & ~(EXTZ(entryMask))) == ((entryVPN) & ~(EXTZ(entryMask)))) &
       ((asid == (entryASID)) | (entryG)))

function option<TLBIndexT> tlbSearch((bit[64]) VAddr) =
  let r    = (VAddr[63..62]) in
  let vpn2 = (VAddr[39..13]) in
  let asid = TLBEntryHi.ASID in
  if (tlbEntryMatch(r, vpn2, asid, TLBEntry00)) then
    Some(0b000)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry01)) then
    Some(0b001)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry02)) then
    Some(0b010)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry03)) then
    Some(0b011)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry04)) then
    Some(0b100)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry05)) then
    Some(0b101)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry06)) then
    Some(0b110)
  else if (tlbEntryMatch(r, vpn2, asid, TLBEntry07)) then
    Some(0b111)
  else
    None

function (bit[64], bool) TLBTranslate2 ((bit[64]) vAddr, (MemAccessType) accessType) = {
  let idx = tlbSearch(vAddr) in
  switch(idx) {
    case (Some(idx)) -> 
    let entry = (TLBEntries[idx]) in
    let entryMask = entry.pagemask in
    
    let evenOddBit = switch(entryMask) {
      case 0x0000 -> 12
      case 0x0003 -> 14
      case 0x000f -> 16
      case 0x003f -> 18
      case 0x00ff -> 20
      case 0x03ff -> 22
      case 0x0fff -> 24
      case 0x3fff -> 26
      case 0xffff -> 28
      case _      -> undefined
    } in
    let isOdd = (vAddr[evenOddBit]) in
    let (caps, capl, (bit[24])pfn, d, v) = if (isOdd) then
        (entry.caps1, entry.capl1, entry.pfn1, entry.d1, entry.v1)
      else
        (entry.caps0, entry.capl0, entry.pfn0, entry.d0, entry.v0) in
    if (~(v)) then 
      exit (SignalExceptionTLB(if (accessType == StoreData) then XTLBInvS else XTLBInvL, vAddr))
    else if ((accessType == StoreData) & ~(d)) then
      exit (SignalExceptionTLB(TLBMod, vAddr))
    else
      (EXTZ(pfn[23..((evenOddBit)-(12))] : vAddr[((evenOddBit)-(1)) .. 0]), 
       if (accessType == StoreData) then caps else capl)
    case None -> exit (SignalExceptionTLB(
      if (accessType == StoreData) then XTLBRefillS else XTLBRefillL, vAddr))
  }
}

function (bit[64], bool) TLBTranslateC ((bit[64]) vAddr, (MemAccessType) accessType) = 
  {
    let currentAccessLevel = getAccessLevel() in
    let compat32 = (vAddr[61..31] == 0b1111111111111111111111111111111) in
    let (requiredLevel, addr) = switch(vAddr[63..62]) {
      case 0b11 -> switch(compat32, vAddr[30..29]) { (* xkseg *)
        case (true, 0b11) -> (Kernel, None)               (* kseg3 mapped 32-bit compat *)
        case (true, 0b10) -> (Supervisor, None)           (* sseg  mapped 32-bit compat *)
        case (true, 0b01) -> (Kernel, Some(EXTZ(vAddr[28..0]))) (* kseg1 unmapped uncached 32-bit compat *)
        case (true, 0b00) -> (Kernel, Some(EXTZ(vAddr[28..0]))) (* kseg0 unmapped cached 32-bit compat *)
        case (_, _) -> (Kernel, None) (* xkseg mapped *)
      }
      case 0b10 -> (Kernel, Some(EXTZ(vAddr[58..0])))       (* xkphys bits 61-59 are cache mode (ignored) *)
      case 0b01 -> (Supervisor, None)                       (* xsseg - supervisor mapped *)
      case 0b00 -> (User, None) (* xuseg - user mapped *)
    } in
    if (((nat)currentAccessLevel) < ((nat)requiredLevel)) then
      exit (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
    else 
      let (pa, c) = switch(addr) {
      case (Some(a)) -> (a, false)
      case None      -> if ((~(compat32)) & (unsigned(vAddr[61..0]) > MAX_VA)) then
          exit (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          TLBTranslate2(vAddr, accessType)
      }
      in if (unsigned(pa) > MAX_PA) then
          exit (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          (pa, c)
  }

function (bit[64]) TLBTranslate ((bit[64]) vAddr, (MemAccessType) accessType) = 
      let (addr, c) = TLBTranslateC(vAddr, accessType) in addr

typedef regno = bit[5]                      (* a register number *)
typedef imm16 = bit[16]                     (* 16-bit immediate *)
(* a commonly used instruction format with three register operands *)
typedef regregreg   = (regno, regno, regno)
(* a commonly used instruction format with two register operands and 16-bit immediate *)
typedef regregimm16 = (regno, regno, imm16)

typedef decode_failure = enumerate { 
  no_matching_pattern; 
  unsupported_instruction; 
  illegal_instruction; 
  internal_error 
}

(* Used by branch and trap instructions *)
typedef Comparison = enumerate { 
  EQ; (* equal *)
  NE; (* not equal *)
  GE; (* signed greater than or equal *)
  GEU;(* unsigned greater than or equal *) 
  GT; (* signed strictly greater than *) 
  LE; (* signed less than or equal *) 
  LT; (* signed strictly less than *) 
  LTU;(* unsigned less than or qual *) 
}
function bool compare ((Comparison)cmp, (bit[64]) valA, (bit[64]) valB) =
   (* sail comparisons are signed so extend to 65 bits for unsigned comparisons *)
  let valA65 = (0b0 : valA) in
  let valB65 = (0b0 : valB) in
  switch(cmp) {
    case EQ  -> valA ==   valB
    case NE  -> valA !=   valB
    case GE  -> valA >=   valB
    case GEU -> valA65 >= valB65
    case GT  -> valA >    valB
    case LE  -> valA <=   valB
    case LT  -> valA <    valB
    case LTU -> valA65 <  valB65
  }
typedef WordType = enumerate { B; H; W; D}

function forall Nat 'r, 'r IN {1,2,4,8}.[:'r:] wordWidthBytes((WordType) w) =
  switch(w) {
    case B -> 1
    case H -> 2
    case W -> 4
    case D -> 8
  }

function bool isAddressAligned(addr, (WordType) wordType) =
  switch (wordType) {
    case B -> true
    case H -> (addr[0]    == 0)
    case W -> (addr[1..0] == 0b00)
    case D -> (addr[2..0] == 0b000)
  }

