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

val tlbEntryMatch : (bits(2), bits(27), bits(8), TLBEntry) -> bool effect pure
function tlbEntryMatch(r, vpn2, asid, entry) =
      let entryValid = entry.valid() in
      let entryR     = entry.r() in
      let entryMask  = entry.pagemask() in
      let entryVPN   = entry.vpn2() in
      let entryASID  = entry.asid() in
      let entryG     = entry.g() in
      let vpnMask : bits(27) = ~(EXTZ(entryMask)) in
      (entryValid &
       (r == entryR) &
       ((vpn2 & vpnMask) == ((entryVPN) & vpnMask)) &
       ((asid == (entryASID)) | (entryG)))

val tlbSearch : bits(64) -> option(TLBIndexT) effect {rreg}
function tlbSearch(VAddr) =
  let r    = (VAddr[63..62]) in
  let vpn2 = (VAddr[39..13]) in
  let asid = TLBEntryHi.ASID() in {
    foreach (idx from 0 to 63) {
      if(tlbEntryMatch(r, vpn2, asid, reg_deref(TLBEntries[idx]))) then
	return Some(to_bits(6, idx))
    };
    None()
  }

/** For given virtual address and accessType returns physical address and
bool flag indicating whether capability stores / loads are permitted for
page (depending on access type). */

val TLBTranslate2 : (bits(64), MemAccessType) -> (bits(64), bool) effect {rreg, wreg, undef, escape}
function TLBTranslate2 (vAddr, accessType) = {
  let idx = tlbSearch(vAddr) in
  match idx {
    Some(idx) =>
      let i as atom(_) = unsigned(idx) in
      let entry = reg_deref(TLBEntries[i]) in
      let entryMask = entry.pagemask() in
      let 'evenOddBit : range(12,28) = match (entryMask) {
        0x0000  => 12,
        0x0003  => 14,
        0x000f  => 16,
        0x003f  => 18,
        0x00ff  => 20,
        0x03ff  => 22,
        0x0fff  => 24,
        0x3fff  => 26,
        0xffff  => 28,
        _       => undefined
      } in
      let isOdd = (vAddr[evenOddBit]) in
      let (caps : bits(1), capl : bits(1), pfn : bits(24), d : bits(1), v : bits(1))  =
        if (isOdd) then
          (entry.caps1(), entry.capl1(), entry.pfn1(), entry.d1(), entry.v1())
        else
          (entry.caps0(), entry.capl0(), entry.pfn0(), entry.d0(), entry.v0()) in
      if (~(v)) then
        SignalExceptionTLB(if (accessType == StoreData) then XTLBInvS else XTLBInvL, vAddr)
      else if ((accessType == StoreData) & ~(d)) then
        SignalExceptionTLB(TLBMod, vAddr)
      else
        let res : bits(64) = EXTZ(pfn[23..(evenOddBit - 12)] @ vAddr[(evenOddBit - 1) .. 0]) in
        (res,  bits_to_bool(if (accessType == StoreData) then caps else capl)),
    None()  =>  SignalExceptionTLB(
      if (accessType == StoreData) then XTLBRefillS else XTLBRefillL, vAddr)
  }
}

val cast_AccessLevel : AccessLevel -> int effect pure
function cast_AccessLevel level =
  match level {
    User        => 0,
    Supervisor  => 1,
    Kernel      => 2
  }

/* perform TLB translation. bool is CHERI specific TLB bits noStoreCap/suppressTag */
val TLBTranslateC : (bits(64), MemAccessType) -> (bits(64), bool) effect {escape, rreg, undef, wreg}
function TLBTranslateC (vAddr, accessType) = 
  {
    let currentAccessLevel = getAccessLevel() in
    let compat32 = (vAddr[61..31] == 0b1111111111111111111111111111111) in
    let (requiredLevel, addr) : (AccessLevel, option(bits(64))) = match (vAddr[63..62]) {
      0b11  => match (compat32, vAddr[30..29]) { /* xkseg */
	(true, 0b11)  => (Kernel, None() : option(bits(64))),               /* kseg3 mapped 32-bit compat */
	(true, 0b10)  => (Supervisor, None() : option(bits(64))),           /* sseg  mapped 32-bit compat */
	(true, 0b01)  => (Kernel, Some(0x00000000 @ 0b000 @ vAddr[28..0])), /* kseg1 unmapped uncached 32-bit compat */
	(true, 0b00)  => (Kernel, Some(0x00000000 @ 0b000 @ vAddr[28..0])), /* kseg0 unmapped cached 32-bit compat */
	(_, _)        => (Kernel, None() : option(bits(64))) /* xkseg mapped */
      },
      0b10  => (Kernel, Some(0b00000 @ vAddr[58..0])), /* xkphys bits 61-59 are cache mode (ignored) */
      0b01  => (Supervisor, None() : option(bits(64))),  /* xsseg - supervisor mapped */
      0b00  => (User, None() : option(bits(64)))         /* xuseg - user mapped */
    } in
    if (cast_AccessLevel(currentAccessLevel) < cast_AccessLevel(requiredLevel)) then
      SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr)
    else
      let (pa, c) : (bits(64), bool) = match addr {
        Some(a) => (a, false),
        None()  => if ((~(compat32)) & (unsigned(vAddr[61..0]) > MAX_VA)) then
            SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr)
          else
            TLBTranslate2(vAddr, accessType)
      }
      in if (unsigned(pa) > MAX_PA) then
          SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr)
        else
          (pa, c)
  }

/* TLB translate function for MIPS (throws away capability flag) */
val TLBTranslate : (bits(64), MemAccessType) -> bits(64) effect {rreg, wreg, escape, undef}
function TLBTranslate (vAddr, accessType) = 
      let (addr, c) = TLBTranslateC(vAddr, accessType) in addr
