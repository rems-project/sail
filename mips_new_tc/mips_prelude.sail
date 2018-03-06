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
  XPTEBase : 63.. 33,
  XR : 32.. 31,
  XBadVPN2 : 30..  4,
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

register TLBEntry00 : TLBEntry
register TLBEntry01 : TLBEntry
register TLBEntry02 : TLBEntry
register TLBEntry03 : TLBEntry
register TLBEntry04 : TLBEntry
register TLBEntry05 : TLBEntry
register TLBEntry06 : TLBEntry
register TLBEntry07 : TLBEntry
register TLBEntry08 : TLBEntry
register TLBEntry09 : TLBEntry
register TLBEntry10 : TLBEntry
register TLBEntry11 : TLBEntry
register TLBEntry12 : TLBEntry
register TLBEntry13 : TLBEntry
register TLBEntry14 : TLBEntry
register TLBEntry15 : TLBEntry
register TLBEntry16 : TLBEntry
register TLBEntry17 : TLBEntry
register TLBEntry18 : TLBEntry
register TLBEntry19 : TLBEntry
register TLBEntry20 : TLBEntry
register TLBEntry21 : TLBEntry
register TLBEntry22 : TLBEntry
register TLBEntry23 : TLBEntry
register TLBEntry24 : TLBEntry
register TLBEntry25 : TLBEntry
register TLBEntry26 : TLBEntry
register TLBEntry27 : TLBEntry
register TLBEntry28 : TLBEntry
register TLBEntry29 : TLBEntry
register TLBEntry30 : TLBEntry
register TLBEntry31 : TLBEntry
register TLBEntry32 : TLBEntry
register TLBEntry33 : TLBEntry
register TLBEntry34 : TLBEntry
register TLBEntry35 : TLBEntry
register TLBEntry36 : TLBEntry
register TLBEntry37 : TLBEntry
register TLBEntry38 : TLBEntry
register TLBEntry39 : TLBEntry
register TLBEntry40 : TLBEntry
register TLBEntry41 : TLBEntry
register TLBEntry42 : TLBEntry
register TLBEntry43 : TLBEntry
register TLBEntry44 : TLBEntry
register TLBEntry45 : TLBEntry
register TLBEntry46 : TLBEntry
register TLBEntry47 : TLBEntry
register TLBEntry48 : TLBEntry
register TLBEntry49 : TLBEntry
register TLBEntry50 : TLBEntry
register TLBEntry51 : TLBEntry
register TLBEntry52 : TLBEntry
register TLBEntry53 : TLBEntry
register TLBEntry54 : TLBEntry
register TLBEntry55 : TLBEntry
register TLBEntry56 : TLBEntry
register TLBEntry57 : TLBEntry
register TLBEntry58 : TLBEntry
register TLBEntry59 : TLBEntry
register TLBEntry60 : TLBEntry
register TLBEntry61 : TLBEntry
register TLBEntry62 : TLBEntry
register TLBEntry63 : TLBEntry

let TLBEntries : vector(64, dec, register(TLBEntry)) = [
    ref TLBEntry63,
    ref TLBEntry62,
    ref TLBEntry61,
    ref TLBEntry60,
    ref TLBEntry59,
    ref TLBEntry58,
    ref TLBEntry57,
    ref TLBEntry56,
    ref TLBEntry55,
    ref TLBEntry54,
    ref TLBEntry53,
    ref TLBEntry52,
    ref TLBEntry51,
    ref TLBEntry50,
    ref TLBEntry49,
    ref TLBEntry48,
    ref TLBEntry47,
    ref TLBEntry46,
    ref TLBEntry45,
    ref TLBEntry44,
    ref TLBEntry43,
    ref TLBEntry42,
    ref TLBEntry41,
    ref TLBEntry40,
    ref TLBEntry39,
    ref TLBEntry38,
    ref TLBEntry37,
    ref TLBEntry36,
    ref TLBEntry35,
    ref TLBEntry34,
    ref TLBEntry33,
    ref TLBEntry32,
    ref TLBEntry31,
    ref TLBEntry30,
    ref TLBEntry29,
    ref TLBEntry28,
    ref TLBEntry27,
    ref TLBEntry26,
    ref TLBEntry25,
    ref TLBEntry24,
    ref TLBEntry23,
    ref TLBEntry22,
    ref TLBEntry21,
    ref TLBEntry20,
    ref TLBEntry19,
    ref TLBEntry18,
    ref TLBEntry17,
    ref TLBEntry16,
    ref TLBEntry15,
    ref TLBEntry14,
    ref TLBEntry13,
    ref TLBEntry12,
    ref TLBEntry11,
    ref TLBEntry10,
    ref TLBEntry09,
    ref TLBEntry08,
    ref TLBEntry07,
    ref TLBEntry06,
    ref TLBEntry05,
    ref TLBEntry04,
    ref TLBEntry03,
    ref TLBEntry02,
    ref TLBEntry01,
    ref TLBEntry00
]

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
function NotWordVal (word) =
    (word[31] ^^ 32) != word[63..32]

/* Read numbered GP reg. (r0 is always zero) */
val rGPR : bits(5) -> bits(64) effect {rreg}
function rGPR idx = {
         let i as atom(_) = unsigned(idx) in
         if i == 0 then 0x0000000000000000 else GPR[i]
}

/* Write numbered GP reg. (writes to r0 ignored) */
val wGPR : (bits(5), bits(64)) -> unit effect {wreg}
function wGPR (idx, v) = {
         let i as atom(_) = unsigned(idx) in
         if i == 0 then () else GPR[i] = v
}

val MEMr = {lem: "MEMr"} : forall 'n.
  ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEMr_reserve = {lem: "MEMr_reserve"} : forall 'n.
  ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
val MEM_sync = {lem: "MEM_sync"} :
  unit -> unit effect { barr }

val MEMea = {lem: "MEMea"} : forall 'n.
  ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMea_conditional = {lem: "MEMea_conditional"} : forall 'n.
  ( bits(64) , atom('n)) -> unit effect { eamem }
val MEMval = {lem: "MEMval"} : forall 'n.
  ( bits(64) , atom('n), bits(8*'n)) -> unit effect { wmv }
val MEMval_conditional = {lem: "MEMval_conditional"} : forall 'n.
  ( bits(64) , atom('n), bits(8*'n)) -> bool effect { wmv }

/* Extern nops with effects, sometimes useful for faking effect */
val skip_eamem = "skip" : unit -> unit effect {eamem}
val skip_barr = "skip" : unit -> unit effect {barr}
val skip_wreg = "skip" : unit -> unit effect {wreg}
val skip_rreg = "skip" : unit -> unit effect {rreg}
val skip_wmvt = "skip" : unit -> unit effect {wmvt}
val skip_rmemt = "skip" : unit -> unit effect {rmemt}
val skip_escape = "skip" : unit -> unit effect {escape}

function MEMr (addr, size) = __MIPS_read(addr, size)
function MEMr_reserve (addr, size) = __MIPS_read(addr, size)
function MEM_sync () = skip_barr()

function MEMea (addr, size) = skip_eamem()
function MEMea_conditional (addr, size) = skip_eamem()
function MEMval (addr, size, data) = __MIPS_write(addr, size, data)
function MEMval_conditional (addr, size, data) = { __MIPS_write(addr, size, data); true }

enum Exception =
{
   Interrupt, TLBMod, TLBL, TLBS, AdEL, AdES, Sys, Bp, ResI, CpU, Ov, Tr, C2E, C2Trap,
   XTLBRefillL, XTLBRefillS, XTLBInvL, XTLBInvS, MCheck
}

/* Return the ISA defined code for an exception condition */
function ExceptionCode (ex) : Exception -> bits(5)=
   let x : bits(8) = match ex
   {
      Interrupt    => 0x00, /* Interrupt */
      TLBMod       => 0x01, /* TLB modification exception */
      TLBL         => 0x02, /* TLB exception (load or fetch) */
      TLBS         => 0x03, /* TLB exception (store) */
      AdEL         => 0x04, /* Address error (load or fetch) */
      AdES         => 0x05, /* Address error (store) */
      Sys          => 0x08, /* Syscall */
      Bp           => 0x09, /* Breakpoint */
      ResI         => 0x0a, /* Reserved instruction */
      CpU          => 0x0b, /* Coprocessor Unusable */
      Ov           => 0x0c, /* Arithmetic overflow */
      Tr           => 0x0d, /* Trap */
      C2E          => 0x12, /* C2E coprocessor 2 exception */
      C2Trap       => 0x12, /* C2Trap maps to same exception code, different vector */
      XTLBRefillL  => 0x02,
      XTLBRefillS  => 0x03,
      XTLBInvL     => 0x02,
      XTLBInvS     => 0x03,
      MCheck       => 0x18
   } in x[4..0]


val SignalExceptionMIPS : forall ('o : Type) . (Exception, bits(64)) -> 'o effect {escape, rreg, wreg}
function SignalExceptionMIPS (ex, kccBase) = 
  {
    /* Only update EPC and BD if not already in EXL mode */
    if (~ (CP0Status.EXL())) then 
      {
        if (inBranchDelay[0]) then
          {
            CP0EPC = PC - 4;
            CP0Cause->BD() = 0b1;
          }
        else
          {
            CP0EPC = PC;
            CP0Cause->BD() = 0b0;
          }
      };

      /* choose an exception vector to branch to. Some are not supported 
         e.g. Reset */
      vectorOffset = 
        if (CP0Status.EXL()) then
          0x180 /* Always use common vector if in exception mode already */
        else if ((ex == XTLBRefillL) | (ex == XTLBRefillS)) then 
          0x080
        else if (ex == C2Trap) then
          0x280 /* Special vector for CHERI traps */
        else
          0x180; /* Common vector */
      vectorBase : bits(64) = if CP0Status.BEV() then
                   0xFFFFFFFFBFC00200
                else
                   0xFFFFFFFF80000000;
      /* On CHERI we have to subtract KCC.base so that we end up at the 
         right absolute vector address after indirecting via new PCC */
      nextPC = vectorBase + EXTS(vectorOffset) - kccBase;
      CP0Cause->ExcCode() = ExceptionCode(ex);
      CP0Status->EXL()    = 0b1;
      throw (ISAException);
  }

/* Defined either in mips_wrappers (directly calling SignalExceptionMIPS) or in cheri_prelude_common (cheri things plus above) */
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
  TLBContext->BadVPN2()  = (badAddr[31..13]);
  TLBXContext->XBadVPN2()= (badAddr[39..13]);
  TLBXContext->XR()      = (badAddr[63..62]);
  TLBEntryHi->R()        = (badAddr[63..62]);
  TLBEntryHi->VPN2()     = (badAddr[39..13]);
  SignalException(ex);
}

enum MemAccessType = {Instruction, LoadData, StoreData}
enum AccessLevel = {User, Supervisor, Kernel} 

function getAccessLevel() : unit -> AccessLevel=
  if ((CP0Status.EXL()) | (CP0Status.ERL())) then
    Kernel
  else match CP0Status.KSU()
    {
      0b00  => Kernel,
      0b01  => Supervisor,
      0b10  => User,
      _     => User /* behaviour undefined, assume user */
    }

val checkCP0Access : unit->unit effect{escape, rreg, wreg}
function checkCP0Access () =
  {
    let accessLevel = getAccessLevel() in
    if ((accessLevel != Kernel) & (~(CP0Status.CU()[0]))) then
      {
        CP0Cause->CE() = 0b00;
        SignalException(CpU);
      }
  }

val incrementCP0Count : unit -> unit effect {rreg,wreg,escape}
function incrementCP0Count() = {
  TLBRandom = (if (TLBRandom == TLBWired)
    then (TLBIndexMax) else (TLBRandom - 1));

  CP0Count = (CP0Count + 1);
  if (CP0Count == CP0Compare) then {
    CP0Cause->IP() = CP0Cause.IP() | 0x80; /* IP7 is timer interrupt  */
  };

  let ims = CP0Status.IM() in
  let ips = CP0Cause.IP() in
  let ie  = CP0Status.IE() in
  let exl = CP0Status.EXL() in
  let erl = CP0Status.ERL() in
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
  match cmp {
    EQ   => valA ==   valB,
    NE   => valA !=   valB,
    GE   => valA >=_s valB,
    GEU  => valA >=_u valB,
    GT   => valB <_s  valA,
    LE   => valB >=_s valA,
    LT   => valA <_s  valB,
    LTU  => valA <_u  valB
  }
enum WordType = { B, H, W, D}

val wordWidthBytes : WordType -> range(1, 8)
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
  a / alignment_width == (a + wordWidthBytes(wordType) - 1) / alignment_width

val reverse_endianness = "reverse_endianness" : forall 'W, 'W >= 1. bits(8 * 'W) -> bits(8 * 'W) effect pure

/*
function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness' (w, value) =
{
    ([:8 * 'W:]) width = length(value);
    if width <= 8
    then value
    else value[7..0] : reverse_endianness'(w - 1, value[(width - 1) .. 8])
}



function rec forall Nat 'W, 'W >= 1. bits(8 * 'W) reverse_endianness ((bits(8 * 'W)) value) =
{
    reverse_endianness'(sizeof 'W, value)
}*/

val MEMr_wrapper : forall 'n, 1 <= 'n <=8 . (bits(64), atom('n)) -> bits(8*'n) effect {rmem}
function MEMr_wrapper (addr, size) = reverse_endianness(MEMr (addr, size))
/* TODO
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

val MEMr_reserve_wrapper : forall 'n, 1 <= 'n <= 8 . ( bits(64) , atom('n) ) -> (bits(8 * 'n)) effect { rmem }
function MEMr_reserve_wrapper (addr , size) =
    reverse_endianness(MEMr_reserve(addr, size))


function init_cp0_state () : unit -> unit = {
  CP0Status->BEV() = bitone;
}

val init_cp2_state : unit -> unit effect {wreg}
val cp2_next_pc:     unit -> unit effect {rreg, wreg}
val dump_cp2_state : unit -> unit effect {rreg, escape}
