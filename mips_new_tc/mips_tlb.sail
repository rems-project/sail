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

function bool tlbEntryMatch(r, vpn2, asid, (TLBEntry) entry) =
      let entryValid = entry.valid in
      let entryR     = entry.r in
      let entryMask  = entry.pagemask in
      let entryVPN   = entry.vpn2 in
      let entryASID  = entry.asid in
      let entryG     = entry.g in
      (entryValid &
       (r == entryR) &
       ((vpn2 & ~((bits(27)) (EXTZ(entryMask)))) == ((entryVPN) & ~((bits(27)) (EXTZ(entryMask))))) &
       ((asid == (entryASID)) | (entryG)))

function option(TLBIndexT) tlbSearch((bits(64)) VAddr) =
  let r    = (VAddr[63..62]) in
  let vpn2 = (VAddr[39..13]) in
  let asid = TLBEntryHi.ASID in {
    foreach (idx from 0 to 63) {
      if(tlbEntryMatch(r, vpn2, asid, (TLBEntries[idx]))) then
	return (Some ((TLBIndexT) (to_vec(idx))))
    };
    None
  }

function (bits(64), bool) TLBTranslate2 ((bits(64)) vAddr, (MemAccessType) accessType) = {
  let idx = tlbSearch(vAddr) in
  match idx {
    (Some(idx))  =>
    let entry = (TLBEntries[idx]) in
    let entryMask = entry.pagemask in

    let evenOddBit = ([|12:28|]) match (bits(16))(entryMask) {
      0x0000  => 12
      0x0003  => 14
      0x000f  => 16
      0x003f  => 18
      0x00ff  => 20
      0x03ff  => 22
      0x0fff  => 24
      0x3fff  => 26
      0xffff  => 28
      _       => undefined
    } in
    let isOdd = (vAddr[evenOddBit]) in
    let if : caps, capl, pfn, d, v (isOdd) then
	((bits(1)) (entry.caps1), (bits(1)) (entry.capl1), (bits(24)) (entry.pfn1), (bits(1)) (entry.d1), (bits(1)) (entry.v1))
      else
	((bits(1)) (entry.caps0), (bits(1)) (entry.capl0), (bits(24)) (entry.pfn0), (bits(1)) (entry.d0), (bits(1)) (entry.v0)) in
    if (~(v)) then
      (SignalExceptionTLB(if (accessType == StoreData) then XTLBInvS else XTLBInvL, vAddr))
    else if ((accessType == StoreData) & ~(d)) then
      (SignalExceptionTLB(TLBMod, vAddr))
    else
      let res = (bits(64)) (EXTZ(pfn[23..(evenOddBit - 12)] : vAddr[(evenOddBit - 1) .. 0])) in
      (res, (bool) (if (accessType == StoreData) then caps else capl)) /* FIXME: get rid of explicit cast here */
    None  =>  (SignalExceptionTLB(
      if (accessType == StoreData) then XTLBRefillS else XTLBRefillL, vAddr))
  }
}

val cast_AccessLevel : cast AccessLevel -> [|0:2|] effect pure

function [|0:2|] cast_AccessLevel level =
{
  switch level {
    User  => 0
    Supervisor  => 1
    Kernel  => 2
  }
}

/* perform TLB translation. bool is CHERI specific TLB bits noStoreCap/suppressTag */
function (bits(64), bool) TLBTranslateC ((bits(64)) vAddr, (MemAccessType) accessType) = 
  {
    let currentAccessLevel = getAccessLevel() in
    let compat32 = (vAddr[61..31] == 0b1111111111111111111111111111111) in
    let AccessLevel : requiredLevel, addr, option(bits(64)))) match (bits(2)) (vAddr[63..62]) {
      0b11  => match compat32, (bits(2)) (vAddr[30..29]) { /* xkseg */
	(true, 0b11)  => (Kernel, (option(bits(64))) None)               /* kseg3 mapped 32-bit compat */
	(true, 0b10)  => (Supervisor, (option(bits(64))) None)           /* sseg  mapped 32-bit compat */
	(true, 0b01)  => (Kernel, Some((bits(64)) (EXTZ(vAddr[28..0])))) /* kseg1 unmapped uncached 32-bit compat */
	(true, 0b00)  => (Kernel, Some((bits(64)) (EXTZ(vAddr[28..0])))) /* kseg0 unmapped cached 32-bit compat */
	(_, _)  => (Kernel, (option(bits(64))) None) /* xkseg mapped */
      }
      0b10  => (Kernel, Some((bits(64)) (EXTZ(vAddr[58..0]))))       /* xkphys bits 61-59 are cache mode (ignored) */
      0b01  => (Supervisor, (option(bits(64))) None)                       /* xsseg - supervisor mapped */
      0b00  => (User, (option(bits(64))) None) /* xuseg - user mapped */
    } in
    if (((nat)currentAccessLevel) < ((nat)requiredLevel)) then
      (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
    else
      let bit : pa, c[64], bool)) match addr {
      (Some(a))  => (a, false)
      None       => if ((~(compat32)) & (unsigned(vAddr[61..0]) > MAX_VA)) then
          (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          TLBTranslate2(vAddr, accessType)
      }
      in if (unsigned(pa) > MAX_PA) then
          (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          (pa, c)
  }

function (bits(64)) TLBTranslate ((bits(64)) vAddr, (MemAccessType) accessType) = 
      let TLBTranslateC : addr, c(vAddr, accessType) in addr
