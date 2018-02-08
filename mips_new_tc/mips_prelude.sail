/*========================================================================*/
/*                                                                        */
/*  Copyright (c) 2015-2017 Robert M. Norton                              */
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

/* mips_prelude.sail: declarations of mips registers, and functions common 
   to mips instructions (e.g. address translation) */

/* bit vectors have indices decreasing from left i.e. msb is highest index */
default Order dec

register PC : bits(64)
register nextPC : bits(64)

/* CP0 Registers */

bitfield CauseReg : bits(32) = {
  BD : 31, /* branch delay */
  /*Z0 : 30,*/
  CE : 29.. 28, /* for coprocessor enable exception */
  /*Z1 : 27.. 24,*/
  IV : 23, /* special interrupt vector not supported */
  WP : 22, /* watchpoint exception occurred */
  /*Z2 : 21.. 16, */
  IP : 15.. 8, /* interrupt pending bits */
  /*Z3 : 7,*/
  ExcCode : 6.. 2, /* code of last exception */
  /*Z4 : 1.. 0,*/
}

bitfield TLBEntryLoReg : bits(64) = {
  CapS : 63,
  CapL : 62,
  PFN : 29.. 6,
  C : 5.. 3,
  D : 2,
  V : 1,
  G : 0,
}

bitfield TLBEntryHiReg : bits(64) = {
  R : 63.. 62,
  VPN2 : 39.. 13,
  ASID : 7..  0,
}

bitfield ContextReg : bits(64) = {
  PTEBase : 63.. 23,
  BadVPN2 : 22.. 4,
  /*ZR : 3.. 0,*/
}

bitfield XContextReg : bits(64) = {
  PTEBase : 63.. 33,
  R : 32.. 31,
  BadVPN2 : 30..  4,
}

let TLBNumEntries = 64
type TLBIndexT = (bits(6))
let TLBIndexMax : TLBIndexT = 0b111111

val MAX : forall 'n. atom('n) -> atom(2 ^ 'n - 1) effect pure
function MAX(n) = pow2(n) - 1

let MAX_U64 = MAX(64) /*unsigned(0xffffffffffffffff)*/
let MAX_VA  = MAX(40) /*unsigned(0xffffffffff)*/
let MAX_PA  = MAX(36) /*unsigned(0xfffffffff)*/

bitfield TLBEntry : bits(117) = {
  pagemask : 116..  101,
  r        : 100..  99,
  vpn2     : 98..  72,
  asid     : 71..  64,
  g        : 63,
  valid    : 62,
  caps1    : 61,
  capl1    : 60,
  pfn1     : 59..  36,
  c1       : 35..  33,
  d1       : 32,
  v1       : 31,
  caps0    : 30,
  capl0    : 29,
  pfn0     : 28..  5,
  c0       : 4..  2,
  d0       : 1,
  v0       : 0,
}

register TLBProbe : bits(1)
register TLBIndex : TLBIndexT
register TLBRandom : TLBIndexT
register TLBEntryLo0 : TLBEntryLoReg
register TLBEntryLo1 : TLBEntryLoReg
register TLBContext : ContextReg
register TLBPageMask : bits(16)
register TLBWired : TLBIndexT
register TLBEntryHi : TLBEntryHiReg
register TLBXContext : XContextReg

register TLBEntries : vector(64, dec, TLBEntry)

register CP0Compare : bits(32)
register CP0Cause : CauseReg
register CP0EPC : bits(64)
register CP0ErrorEPC : bits(64)
register CP0LLBit : bits(1)
register CP0LLAddr : bits(64)
register CP0BadVAddr : bits(64)
register CP0Count : bits(32)
register CP0HWREna : bits(32)
register CP0UserLocal : bits(64)

bitfield StatusReg : bits(32) = {
  CU : 31.. 28,  /* co-processor enable bits */
  /* RP/FR/RE/MX/PX not implemented */
  BEV : 22, /* use boot exception vectors (initialised to one) */
  /* TS/SR/NMI not implemented */
  IM : 15.. 8,  /* Interrupt mask */
  KX : 7,  /* kernel 64-bit enable */
  SX : 6,  /* supervisor 64-bit enable */
  UX : 5,  /* user 64-bit enable */
  KSU : 4.. 3, /* Processor mode */
  ERL : 2, /* error level (should be initialised to one, but BERI is different) */
  EXL : 1, /* exception level */
  IE : 0,  /* interrupt enable */
}
register CP0Status : StatusReg

/* Implementation registers -- not ISA defined */
register branchPending : bits(1)      /* Set by branch instructions to implement branch delay */
register inBranchDelay : bits(1)      /* Needs to be set by outside world when in branch delay slot */
register delayedPC : bits(64)          /* Set by branch instructions to implement branch delay */

/* General purpose registers */


/* Special registers For MUL/DIV */
register HI : bits(64)
register LO : bits(64)

register GPR : vector(32, dec, bits(64))

/* JTAG Uart registers */

register UART_WDATA : bits(8)
register UART_WRITTEN : bits(1)
register UART_RDATA : bits(8)
register UART_RVALID : bits(1)

/* Check whether a given 64-bit vector is a properly sign extended 32-bit word */
val NotWordVal : bits(64) -> bool effect pure
function bool NotWordVal (word) =
    (word[31] ^^ 32) != word[63..32]

/* Read numbered GP reg. (r0 is always zero) */
val rGPR : bits(5) -> bits(64) effect {rreg}
function rGPR idx = {
         if idx == 0 then 0 else GPR[idx]
}

/* Write numbered GP reg. (writes to r0 ignored) */
val wGPR : (bits(5), bits(64)) -> unit effect {wreg}
function wGPR (idx, v) = {
         if idx == 0 then () else GPR[idx] = v
}

val MEMr         : forall 'n. ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEMr_reserve : forall 'n. ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEM_sync     : unit -> unit effect { barr }

val MEMea              : forall 'n. ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMea_conditional  : forall 'n. ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMval             : forall 'n. ( bits(64) , atom('n), bits(8*'n)) -> unit effect { wmv }
val MEMval_conditional : forall 'n. ( bits(64) , atom('n), bits(8*'n)) -> bool effect { wmv }

enum Exception =
{
   Interrupt, TLBMod, TLBL, TLBS, AdEL, AdES, Sys, Bp, ResI, CpU, Ov, Tr, C2E, C2Trap,
   XTLBRefillL, XTLBRefillS, XTLBInvL, XTLBInvS, MCheck
}

/* Return the ISA defined code for an exception condition */
function ExceptionCode (ex) : Exception -> bits(5)=
   match ex
   {
      Interrupt    => mask(0x00), /* Interrupt */
      TLBMod       => mask(0x01), /* TLB modification exception */
      TLBL         => mask(0x02), /* TLB exception (load or fetch) */
      TLBS         => mask(0x03), /* TLB exception (store) */
      AdEL         => mask(0x04), /* Address error (load or fetch) */
      AdES         => mask(0x05), /* Address error (store) */
      Sys          => mask(0x08), /* Syscall */
      Bp           => mask(0x09), /* Breakpoint */
      ResI         => mask(0x0a), /* Reserved instruction */
      CpU          => mask(0x0b), /* Coprocessor Unusable */
      Ov           => mask(0x0c), /* Arithmetic overflow */
      Tr           => mask(0x0d), /* Trap */
      C2E          => mask(0x12), /* C2E coprocessor 2 exception */
      C2Trap       => mask(0x12), /* C2Trap maps to same exception code, different vector */
      XTLBRefillL  => mask(0x02),
      XTLBRefillS  => mask(0x03),
      XTLBInvL     => mask(0x02),
      XTLBInvS     => mask(0x03),
      MCheck       => mask(0x18)
   }


val SignalExceptionMIPS : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape}
function SignalExceptionMIPS (ex, kccBase) = 
  {
    /* Only update EPC and BD if not already in EXL mode */
    if (~ (CP0Status.EXL)) then 
      {
        if (inBranchDelay[0]) then
          {
            CP0EPC = PC - 4;
            CP0Cause.BD = 1;
          }
        else
          {
            CP0EPC = PC;
            CP0Cause.BD = 0;
          }
      };

      /* choose an exception vector to branch to. Some are not supported 
         e.g. Reset */
      vectorOffset = 
        if (CP0Status.EXL) then
          0x180 /* Always use common vector if in exception mode already */
        else if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) then 
          0x080
        else if (ex == C2Trap) then
          0x280 /* Special vector for CHERI traps */
        else
          0x180; /* Common vector */
      vectorBase : bits(64) = if CP0Status.BEV then
                   0xFFFFFFFFBFC00200
                else
                   0xFFFFFFFF80000000;
      /* On CHERI we have to subtract KCC.base so that we end up at the 
         right absolute vector address after indirecting via new PCC */
      nextPC = vectorBase + EXTS(vectorOffset) - kccBase;
      CP0Cause.ExcCode      = ExceptionCode(ex);
      CP0Status.EXL         = 1;
      exit (());
  }

val SignalException : forall ('o : Type) . Exception -> 'o effect {escape, rreg, wreg}

val SignalExceptionBadAddr : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape, rreg, wreg}
function  SignalExceptionBadAddr(ex, badAddr) =
  {
    CP0BadVAddr = badAddr;
    SignalException(ex);
  }

val SignalExceptionTLB : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape, rreg, wreg}
function SignalExceptionTLB(ex, badAddr) = {
  CP0BadVAddr = badAddr;
  (TLBContext.BadVPN2) = (badAddr[31..13]);
  (TLBXContext.BadVPN2)= (badAddr[39..13]);
  (TLBXContext.R)      = (badAddr[63..62]);
  (TLBEntryHi.R)       = (badAddr[63..62]);
  (TLBEntryHi.VPN2)    = (badAddr[39..13]);
  SignalException(ex);
}

enum MemAccessType = {Instruction, LoadData, StoreData}
enum AccessLevel = {User, Supervisor, Kernel} 

function getAccessLevel() : unit -> AccessLevel=
  if ((CP0Status.EXL) | (CP0Status.ERL)) then
    Kernel
  else match CP0Status.KSU
    {
      0b00  => Kernel,
      0b01  => Supervisor,
      0b10  => User,
      _     => User /* behaviour undefined, assume user */
    }

function checkCP0Access () =
  {
    let accessLevel = getAccessLevel() in
    if ((accessLevel != Kernel) & (~(CP0Status[28] /*CU0*/))) then
      {
        (CP0Cause.CE) = 0b00;
        SignalException(CpU);
      }
  }

function incrementCP0Count() = {
  TLBRandom = (if (TLBRandom == TLBWired)
    then (TLBIndexMax) else (TLBRandom - 1));

  CP0Count = (CP0Count + 1);
  if (CP0Count == CP0Compare) then {
    (CP0Cause[15]) = bitone; /* XXX indexing IP field here doesn't seem to work  */
  };

  let ims = CP0Status.IM in
  let ips = CP0Cause.IP in
  let ie  = CP0Status.IE in
  let exl = CP0Status.EXL in
  let erl = CP0Status.ERL in
  if ((~(exl)) & (~(erl)) & ie & ((ips & ims) != 0x00)) then
    SignalException(Interrupt);
}

type regno = bits(5)                      /* a register number */
type imm16 = bits(16)                     /* 16-bit immediate */
/* a commonly used instruction format with three register operands */
type regregreg = (regno, regno, regno)
/* a commonly used instruction format with two register operands and 16-bit immediate */
type regregimm16 = (regno, regno, imm16)

enum decode_failure = { 
  no_matching_pattern, 
  unsupported_instruction, 
  illegal_instruction, 
  internal_error
}

/* Used by branch and trap instructions */
enum Comparison = { 
  EQ, /* equal */
  NE, /* not equal */
  GE, /* signed greater than or equal */
  GEU,/* unsigned greater than or equal */ 
  GT, /* signed strictly greater than */ 
  LE, /* signed less than or equal */ 
  LT, /* signed strictly less than */ 
  LTU /* unsigned less than or qual */ 
}

val compare : (Comparison, bits(64), bits(64)) -> bool
function compare (cmp, valA, valB) =
   /* sail comparisons are signed so extend to 65 bits for unsigned comparisons */
  let valA65 = (0b0 : valA) in
  let valB65 = (0b0 : valB) in
  match cmp {
    EQ   => valA ==   valB,
    NE   => valA !=   valB,
    GE   => valA >=   valB,
    GEU  => valA65 >= valB65,
    GT   => valA >    valB,
    LE   => valA <=   valB,
    LT   => valA <    valB,
    LTU  => valA65 <  valB65
  }
enum WordType = { B, H, W, D}

val wordWidthBytes : Wordwidthbytes -> range(1, 8)
function wordWidthBytes(w) =
  match w {
    B  => 1,
    H  => 2,
    W  => 4,
    D  => 8
  }

/* This function checks that memory accesses are naturally aligned
   -- it is disabled in favour of BERI specific behaviour below.
function bool isAddressAligned(addr, (WordType) wordType) =
  match wordType {
    B  => true
    H  => (addr[0]    == 0)
    W  => (addr[1..0] == 0b00)
    D  => (addr[2..0] == 0b000)
  }
*/

/* BERI relaxes the natural alignment requirement for loads and stores
   but still throws an exception if an access spans a cache line
   boundary.  Here we assume this is 32 bytes so that we don't have to
   worry about clearing multiple tags when an access spans more than
   one capability. Capability load/stores are still naturally
   aligned. Provided this is a factor of smallest supported page size
   (4k) we don't need to worry about accesses spanning page boundaries
   either.
*/
let alignment_width = 16
val isAddressAligned : (bits(64), WordType) -> bool
function isAddressAligned (addr, wordType) =
  let a = unsigned(addr) in
  quot(a, alignment_width) == quot(a + wordWidthBytes(wordType) - 1, alignment_width)

/*val reverse_endianness : forall Nat 'W, 'W >= 1. ([:'W:], bits(8 * 'W)) -> bits(8 * 'W) effect pure'

function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness' (w, value) =
{
    ([:8 * 'W:]) width = length(value);
    if width <= 8
    then value
    else value[7..0] : reverse_endianness'(w - 1, value[(width - 1) .. 8])
}

val reverse_endianness : forall Nat 'W, 'W >= 1. bits(8 * 'W) -> bits(8 * 'W) effect pure

function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness ((bits(8 * 'W)) value) =
{
    reverse_endianness'(sizeof 'W, value)
}*/

val MEMr_wrapper : forall 'n, 1 <= 'n <=8 . (bits(64), atom('n)) -> bits(8*n) effect {rmem}
function MEMr_wrapper (addr, size) = reverse_endianness(MEMr (addr, size)) /* TODO
    if (addr == 0x000000007f000000) then
      {
        let rvalid = UART_RVALID in
	let rdata = (bits(8 * 'n)) (mask(0x00000000 : UART_RDATA : rvalid : 0b0000000 : 0x0000)) in
        {
          UART_RVALID = [bitzero];
          rdata
        }
      }
    else if (addr == 0x000000007f000004) then
      mask(0x000000000004ffff) /* Always plenty of write space available and jtag activity */
    else
      reverse_endianness(MEMr(addr, size)) /* MEMr assumes little endian */ */

val MEMr_reserve_wrapper : forall 'n. ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
function MEMr_reserve_wrapper (addr , size) =
    reverse_endianness(MEMr_reserve(addr, size))
