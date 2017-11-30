(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Robert M. Norton                              *)
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
  let asid = TLBEntryHi.ASID in {
    foreach (idx from 0 to 63) {
      if(tlbEntryMatch(r, vpn2, asid, (TLBEntries[idx]))) then
        return (Some ((TLBIndexT) idx))
    };
    None
  }

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
      (SignalExceptionTLB(if (accessType == StoreData) then XTLBInvS else XTLBInvL, vAddr))
    else if ((accessType == StoreData) & ~(d)) then
      (SignalExceptionTLB(TLBMod, vAddr))
    else
      (EXTZ(pfn[23..((evenOddBit)-(12))] : vAddr[((evenOddBit)-(1)) .. 0]), 
       if (accessType == StoreData) then caps else capl)
    case None ->  (SignalExceptionTLB(
      if (accessType == StoreData) then XTLBRefillS else XTLBRefillL, vAddr))
  }
}

(* perform TLB translation. bool is CHERI specific TLB bits noStoreCap/suppressTag *)
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
    if ((int_of_accessLevel(currentAccessLevel)) < (int_of_accessLevel(requiredLevel))) then
      (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
    else 
      let (pa, c) = switch(addr) {
      case (Some(a)) -> (a, false)
      case None      -> if ((~(compat32)) & (unsigned(vAddr[61..0]) > MAX_VA)) then
          (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          TLBTranslate2(vAddr, accessType)
      }
      in if (unsigned(pa) > MAX_PA) then
          (SignalExceptionBadAddr(if (accessType == StoreData) then AdES else AdEL, vAddr))
        else
          (pa, c)
  }

function (bit[64]) TLBTranslate ((bit[64]) vAddr, (MemAccessType) accessType) = 
      let (addr, c) = TLBTranslateC(vAddr, accessType) in addr
