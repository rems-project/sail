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

(* Old encodings *)
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b000) = Some(CGetPerm(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b001) = Some(CGetType(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b010) = Some(CGetBase(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b011) = Some(CGetLen(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b101) = Some(CGetTag(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : 0b00000000 : 0b110) = Some(CGetSealed(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd :    0b00000 : 0b00000000 : 0b100) = Some(CGetCause(rd))

function clause decode (0b010010 : 0b00110 : 0b000000000000000000000) = Some(CReturn)

function clause decode (0b010010 : 0b01101 : (regno) rd : (regno) cb : 0b00000000 : 0b010) = Some(CGetOffset(rd, cb)) (* NB encoding does not follow pattern *)
function clause decode (0b010010 : 0b00100 : 0b00000 : 0b00000 : (regno) rt : 0b000 : 0b100) = Some(CSetCause(rt))
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b000) = Some(CAndPerm(cd, cb, rt))
function clause decode (0b010010 : 0b01100 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b000) = Some(CToPtr(rd, cb, ct))

function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b000) = Some(CPtrCmp(rd, cb, ct, CEQ))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b001) = Some(CPtrCmp(rd, cb, ct, CNE))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b010) = Some(CPtrCmp(rd, cb, ct, CLT))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b011) = Some(CPtrCmp(rd, cb, ct, CLE))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b100) = Some(CPtrCmp(rd, cb, ct, CLTU))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b101) = Some(CPtrCmp(rd, cb, ct, CLEU))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b110) = Some(CPtrCmp(rd, cb, ct, CEXEQ))
function clause decode (0b010010 : 0b01110 : (regno) rd : (regno) cb : (regno) ct : 0b000 : 0b111) = Some(CPtrCmp(rd, cb, ct, CNEXEQ))
function clause decode (0b010010 : 0b01101 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b000) = Some(CIncOffset(cd, cb, rt))
function clause decode (0b010010 : 0b01101 : (regno) cd : (regno) cb : (regno) rt : 0b000 : 0b001) = Some(CSetOffset(cd, cb, rt))
function clause decode (0b010010 : 0b00001 : (regno) cd : (regno) cb : (regno) rt : 0b000000)      = Some(CSetBounds(cd, cb, rt))

function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : 0b00000 : 0b000: 0b101)    = Some(CClearTag(cd, cb))
function clause decode (0b010010 : 0b00100 : (regno) cd : (regno) cb : (regno) rt : 0b000: 0b111) = Some(CFromPtr(cd, cb, rt))
function clause decode (0b010010 : 0b01011 : (regno) cs : 0b00000 : (regno) rt : 0b000: 0b000) = Some(CCheckPerm(cs, rt))
function clause decode (0b010010 : 0b01011 : (regno) cs : (regno) cb : 0b00000 : 0b000: 0b001) = Some(CCheckType(cs, cb))
function clause decode (0b010010 : 0b00010 : (regno) cd : (regno) cs : (regno) ct : 0b000: 0b000) = Some(CSeal(cd, cs, ct))
function clause decode (0b010010 : 0b00011 : (regno) cd : (regno) cs : (regno) ct : 0b000: 0b000) = Some(CUnseal(cd, cs, ct))
function clause decode (0b010010 : 0b00111 : (regno) cd : (regno) cb : 0b00000 : 0b000000) = Some(CJALR(cd, cb, true)) (* CJALR *)
function clause decode (0b010010 : 0b01000 : 0b00000    : (regno) cb : 0b00000 : 0b000000) = Some(CJALR(0b00000, cb, false)) (* CJR *)


(* 
New encodings as per CHERI ISA Appendix B.2.  

NB: Must be careful about order of matching because unused register
fields are re-used as additional function codes.
*)

(* One arg *)
function clause decode (0b010010 : 0b00000 : (regno) rd :    0b00001 :    0b11111 : 0b111111) = Some(CGetCause(rd))
function clause decode (0b010010 : 0b00000 : (regno) rs :    0b00010 :    0b11111 : 0b111111) = Some(CSetCause(rs))
function clause decode (0b010010 : 0b00000 : (regno) cd :    0b00000 :    0b11111 : 0b111111) = Some(CGetPCC(cd))

(* Two arg *)
function clause decode (0b010010 : 0b00000 : (regno) cs : (regno) rt :    0b01000 : 0b111111) = Some(CCheckPerm(cs, rt))
function clause decode (0b010010 : 0b00000 : (regno) cs : (regno) cb :    0b01001 : 0b111111) = Some(CCheckType(cs, cb))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cb :    0b01011 : 0b111111) = Some(CClearTag(cd, cb))

(* Capability Inspection *)
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00000 : 0b111111) = Some(CGetPerm(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00001 : 0b111111) = Some(CGetType(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00010 : 0b111111) = Some(CGetBase(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00011 : 0b111111) = Some(CGetLen(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00100 : 0b111111) = Some(CGetTag(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00101 : 0b111111) = Some(CGetSealed(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb :    0b00110 : 0b111111) = Some(CGetOffset(rd, cb))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) rs :    0b00111 : 0b111111) = Some(CGetPCCSetOffset(cd, rs))

(* Three operand *)

(* Capability Modification *)
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) ct : 0b001011) = Some(CSeal(cd, cs, ct))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) ct : 0b001100) = Some(CUnseal(cd, cs, ct))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rt : 0b001101) = Some(CAndPerm(cd, cs, rt))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rt : 0b001111) = Some(CSetOffset(cd, cs, rt))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rt : 0b001000) = Some(CSetBounds(cd, cs, rt))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rt : 0b001001) = Some(CSetBoundsExact(cd, cs, rt))


function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cb : (regno) rt : 0b010001) = Some(CIncOffset(cd, cb, rt))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cb : (regno) ct : 0b011101) = Some(CBuildCap(cd, cb, ct))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cb : (regno) ct : 0b011110) = Some(CCopyType(cd, cb, ct))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) ct : 0b011111) = Some(CCSeal(cd, cs, ct))

(* Pointer Arithmetic *)
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) ct : 0b010010) = Some(CToPtr(rd, cb, ct))
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cb : (regno) rs : 0b010011) = Some(CFromPtr(cd, cb, rs))
function clause decode (0b010010 : 0b00000 : (regno) rt : (regno) cb : (regno) cs : 0b001010) = Some(CSub(rt, cb, cs))
(* XXX function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs :    0b01010 : 0b111111) = Some(CMove(cd, cs)) *)
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rs : 0b011011) = Some(CMOVX(cd, cs, rs, false)) (* CMOVZ *)
function clause decode (0b010010 : 0b00000 : (regno) cd : (regno) cs : (regno) rs : 0b011100) = Some(CMOVX(cd, cs, rs, true))  (* CMOVN *)

(* Pointer Comparison *)
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b010100) = Some(CPtrCmp(rd, cb, cs, CEQ))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b010101) = Some(CPtrCmp(rd, cb, cs, CNE))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b010110) = Some(CPtrCmp(rd, cb, cs, CLT))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b010111) = Some(CPtrCmp(rd, cb, cs, CLE))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b011000) = Some(CPtrCmp(rd, cb, cs, CLTU))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b011001) = Some(CPtrCmp(rd, cb, cs, CLEU))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b011010) = Some(CPtrCmp(rd, cb, cs, CEXEQ))
function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) cs : 0b100001) = Some(CPtrCmp(rd, cb, cs, CNEXEQ))

(* function clause decode (0b010010 : 0b00000 : (regno) rd : (regno) cb : (regno) ct : 0b100000) = Some(CTestSubset(rd, cb, ct)) *)

function clause decode (0b010010 : 0b01001 : (regno) cd : (bit[16]) imm) = Some(CBX(cd, imm, true))  (* CBTU *)
function clause decode (0b010010 : 0b01010 : (regno) cd : (bit[16]) imm) = Some(CBX(cd, imm, false)) (* CBTS *)
function clause decode (0b010010 : 0b10001 : (regno) cd : (bit[16]) imm) = Some(CBZ(cd, imm, false)) (* CBEZ *)
function clause decode (0b010010 : 0b10010 : (regno) cd : (bit[16]) imm) = Some(CBZ(cd, imm, true))  (* CBNZ *)

function clause decode (0b010010 : 0b00101 :    0b00000 :    0b00000 : 0b11111111111) = Some(CReturn)
function clause decode (0b010010 : 0b00101 : (regno) cs : (regno) cb : (bit[11]) selector) = Some(CCall(cs, cb, selector))

function clause decode (0b010010 : 0b01111 : 0b00000 : (bit[16]) imm) = Some(ClearRegs(GPLo, imm))
function clause decode (0b010010 : 0b01111 : 0b00001 : (bit[16]) imm) = Some(ClearRegs(GPHi, imm))
function clause decode (0b010010 : 0b01111 : 0b00010 : (bit[16]) imm) = Some(ClearRegs(CLo,  imm))
function clause decode (0b010010 : 0b01111 : 0b00011 : (bit[16]) imm) = Some(ClearRegs(CHi,  imm))

(* XXX CSetBoundsImmediate *)
(* XXX CIncOffsetImmediate *)

function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b00) = Some(CLoad(rd, cb, rt, offset, false, B, false)) (* CLBU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b00) = Some(CLoad(rd, cb, rt, offset, true,  B, false)) (* CLB *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b01) = Some(CLoad(rd, cb, rt, offset, false, H, false)) (* CLHU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b01) = Some(CLoad(rd, cb, rt, offset, true,  H, false)) (* CLH *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b10) = Some(CLoad(rd, cb, rt, offset, false, W, false)) (* CLWU *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b1 : 0b10) = Some(CLoad(rd, cb, rt, offset, true,  W, false)) (* CLW *)
function clause decode (0b110010 : (regno) rd : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b11) = Some(CLoad(rd, cb, rt, offset, false, D, false)) (* CLD *)

function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, B, true)) (* CLLBU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  B, true)) (* CLLB  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, H, true)) (* CLLHU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  H, true)) (* CLLH  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, W, true)) (* CLLWU *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b1 : 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  W, true)) (* CLLW  *)
function clause decode (0b010010 : 0b10000 : (regno) rd : (regno) cb : 0b00000001 : 0b0 : 0b11) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, D, true)) (* CLLD  *)

function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b00) = Some(CStore(rs, cb, rt, 0b00000, offset, B, false)) (* CSB *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b01) = Some(CStore(rs, cb, rt, 0b00000, offset, H, false)) (* CSH *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b10) = Some(CStore(rs, cb, rt, 0b00000, offset, W, false)) (* CSW *)
function clause decode (0b111010 : (regno) rs : (regno) cb: (regno) rt : (bit[8]) offset : 0b0 : 0b11) = Some(CStore(rs, cb, rt, 0b00000, offset, D, false)) (* CSD *)

function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b00) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, B, true)) (* CSCB *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b01) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, H, true)) (* CSCH *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b10) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, W, true)) (* CSCW *)
function clause decode (0b010010 : 0b10000 : (regno) rs : (regno) cb : (regno) rd : 0b0000 : 0b11) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, D, true)) (* CSCD *)

function clause decode (0b111110 : (regno) cs : (regno) cb: (regno) rt : (bit[11]) offset) = Some(CSC(cs, cb, rt, 0b00000, offset, false))
function clause decode (0b010010 : 0b10000 : (regno) cs : (regno) cb: (regno) rd : 0b00 : 0b0111) = Some(CSC(cs, cb, 0b00000, rd, 0b00000000000, true))

function clause decode (0b110110 : (regno) cd : (regno) cb: (regno) rt : (bit[11]) offset) = Some(CLC(cd, cb, rt, offset, false))
function clause decode (0b010010 : 0b10000 : (regno) cd : (regno) cb: 0b0000000 : 0b1111) = Some(CLC(cd, cb, 0b00000, 0b00000000000, true))

function clause decode (0b010010 : 0b00100 : (regno) rt : 0x0006) = Some(C2Dump(rt))

(* Operations that extract parts of a capability into GPR *)

union ast member (regno, regno) CGetPerm
union ast member (regno, regno) CGetType
union ast member (regno, regno) CGetBase
union ast member (regno, regno) CGetLen
union ast member (regno, regno) CGetTag
union ast member (regno, regno) CGetSealed
union ast member (regno, regno) CGetOffset

function clause execute (CGetPerm(rd, cb)) =
{
  (* START_CGetPerms *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := EXTZ(getCapPerms(capVal));
  (* END_CGetPerms *)
}

function clause execute (CGetType(rd, cb)) =
{
  (* START_CGetType *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := if (capVal.sealed)
      then EXTZ(capVal.otype)
      else -1
  (* END_CGetType *)
}

function clause execute (CGetBase(rd, cb)) =
{
  (* START_CGetBase *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := (bit[64]) (getCapBase(capVal));
  (* END_CGetBase *)
}

function clause execute (CGetOffset(rd, cb)) =
{
  (* START_CGetOffset *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := (bit[64]) (getCapOffset(capVal));
  (* END_CGetOffset *)
}

function clause execute (CGetLen(rd, cb)) =
{
  (* START_CGetLen *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    let len65  = getCapLength(capVal) in
    let len64  = (if len65 > MAX_U64 then MAX_U64 else len65) in
    wGPR(rd) := (bit[64]) len64;
  (* END_CGetLen *)
}

function clause execute (CGetTag(rd, cb)) =
{
  (* START_CGetTag *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := EXTZ(capVal.tag);
  (* END_CGetTag *)
}

function clause execute (CGetSealed(rd, cb)) =
{
  (* START_CGetSealed *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) := EXTZ(capVal.sealed);
  (* END_CGetSealed *)
}

union ast member regno CGetPCC
function clause execute (CGetPCC(cd)) =
{
  (* START_CGetPCC *)
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else
    let pcc = (capRegToCapStruct(PCC)) in
    let (success, pcc2) = setCapOffset(pcc, PC) in
    {assert (success, None); (* guaranteed to be in-bounds *)
    writeCapReg(cd, pcc2)};
  (* END_CGetPCC *)
}


union ast member (regno, regno) CGetPCCSetOffset
function clause execute (CGetPCCSetOffset(cd, rs)) =
{
  (* START_CGetPCCSetOffset *)
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else
    let pcc = (capRegToCapStruct(PCC)) in
    let rs_val = rGPR(rs) in
    let (success, newPCC) = setCapOffset(pcc, rs_val) in
    if (success) then
        writeCapReg(cd, newPCC)
    else
        writeCapReg(cd, int_to_cap(rs_val));
  (* END_CGetPCCSetOffset *)
}
(* Get and Set CP2 cause register *)

union ast member regno CGetCause
function clause execute (CGetCause(rd)) = 
{
  (* START_CGetCause *)
  checkCP2usable();
  if not (pcc_access_system_regs ()) then
    raise_c2_exception_noreg(CapEx_AccessSystemRegsViolation)
  else
    wGPR(rd) := EXTZ(CapCause)
  (* END_CGetCause *)
}

union ast member (regno) CSetCause
function clause execute (CSetCause((regno) rt)) = 
{
  (* START_CSetCause *)
  checkCP2usable();
  if not (pcc_access_system_regs ()) then
    raise_c2_exception_noreg(CapEx_AccessSystemRegsViolation)
  else
    {
      (bit[64]) rt_val := rGPR(rt);
      CapCause.ExcCode := rt_val[15..8];
      CapCause.RegNum  := rt_val[7..0];
    }
  (* END_CSetCause *)
}

union ast member regregreg CAndPerm
function clause execute(CAndPerm(cd, cb, rt)) = 
{
  (* START_CAndPerm *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := rGPR(rt);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    let perms   = getCapPerms(cb_val) in
    let newCap  = setCapPerms(cb_val, (perms & rt_val[30..0])) in
    writeCapReg(cd, newCap);
  (* END_CAndPerm *)
}



union ast member regregreg CToPtr
function clause execute(CToPtr(rd, cb, ct)) = 
{
  (* START_CToPtr *)
  checkCP2usable();
  ct_val := readCapReg(ct);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (ct_val.tag) then
    raise_c2_exception(CapEx_TagViolation, ct)
  else if (cb_val.tag) & (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else 
    {
      let cbBase = getCapBase(cb_val) in
      let cbTop = getCapTop(cb_val) in
      let ctBase = getCapBase(ct_val) in
      let ctTop = getCapTop(ct_val) in
      wGPR(rd) := if (not (cb_val.tag)) |
                     (cbBase < ctBase) |
                     (cbTop > ctTop) then
          ((bit[64]) 0)
        else
          (bit[64])(getCapCursor(cb_val) - ctBase)
    }
  (* END_CToPtr *)
}



union ast member regregreg CSub
function clause execute(CSub(rd, cb, ct)) = 
{
  (* START_CSub *)
  checkCP2usable();
  ct_val := readCapReg(ct);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else 
    {
      wGPR(rd) := (bit[64])(getCapCursor(cb_val) - getCapCursor(ct_val))
    }
  (* END_CSub *)
}

union ast member (regno, regno, regno, CPtrCmpOp) CPtrCmp
function clause execute(CPtrCmp(rd, cb, ct, op)) = 
{
  (* START_CPtrCmp *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else 
    {
      cb_val := readCapReg(cb);
      ct_val := readCapReg(ct);
      equal  := false;
      ltu    := false;
      lts    := false;
      if (cb_val.tag != ct_val.tag) then
        {
          if not (cb_val.tag) then
            {
              ltu := true;
              lts := true;
            }
        }
      else
        {
          cursor1 := getCapCursor(cb_val);
          cursor2 := getCapCursor(ct_val);
          equal   := (cursor1 == cursor2);
          ltu     := (cursor1 < cursor2);
          lts     := (((bit[64])cursor1) <_s ((bit[64])cursor2));
        };
      wGPR(rd) := EXTZ(switch (op) {
        case CEQ   -> [equal]
        case CNE   -> [not (equal)]
        case CLT   -> [lts]
        case CLE   -> [lts | equal]
        case CLTU  -> [ltu]
        case CLEU  -> [ltu | equal]
        case CEXEQ -> [cb_val == ct_val]
        case CNEXEQ -> [cb_val != ct_val]
      })
    }
  (* END_CPtrCmp *)
}

union ast member regregreg CIncOffset
function clause execute (CIncOffset(cd, cb, rt)) =
{
  (* START_CIncOffset *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := rGPR(rt);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if ((cb_val.tag) & (cb_val.sealed) & (rt_val != 0x0000000000000000)) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    let (success, newCap) = incCapOffset(cb_val, rt_val) in
    if (success) then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(getCapBase(cb_val) + rt_val))
  (* END_CIncOffset *)
}

union ast member regregreg CSetOffset
function clause execute (CSetOffset(cd, cb, rt)) =
{
  (* START_CSetOffset *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := rGPR(rt);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if ((cb_val.tag) & (cb_val.sealed)) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    let (success, newCap) = setCapOffset(cb_val, rt_val) in
    if (success) then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(getCapBase(cb_val) + rt_val))
  (* END_CSetOffset *)
}

union ast member regregreg CSetBounds
function clause execute (CSetBounds(cd, cb, rt)) =
{
  (* START_CSetBounds *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := unsigned(rGPR(rt));
  cursor := getCapCursor(cb_val);
  base   := getCapBase(cb_val);
  top    := getCapTop(cb_val);
  newTop := cursor + rt_val;
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if (cursor < base) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if (newTop > top) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else
    let (_, newCap) = setCapBounds(cb_val, (bit[64]) cursor, (bit[65]) newTop) in
    writeCapReg(cd, newCap) (* ignore exact *)
  (* END_CSetBounds *)
}


union ast member regregreg CSetBoundsExact
function clause execute (CSetBoundsExact(cd, cb, rt)) =
{
  (* START_CSetBoundsExact *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := unsigned(rGPR(rt));
  cursor := getCapCursor(cb_val);
  base   := getCapBase(cb_val);
  top    := getCapTop(cb_val);
  newTop := cursor + rt_val;
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if (cursor < base) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if (newTop > top) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else
    let (exact, newCap) = setCapBounds(cb_val, (bit[64]) cursor, (bit[65]) newTop) in
    if not (exact) then
        raise_c2_exception(CapEx_InexactBounds, cb)
    else
        writeCapReg(cd, newCap)
  (* END_CSetBoundsExact *)
}

union ast member (regno, regno) CClearTag
function clause execute (CClearTag(cd, cb)) =
{
  (* START_CClearTag *)
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    {
      cb_val := readCapReg(cb);
      writeCapReg(cd, {cb_val with tag = false});
    }
  (* END_CClearTag *)
}

union ast member (regno,regno,regno,bool) CMOVX
function clause execute (CMOVX(cd, cb, rt, ismovn)) =
{
  (* START_CMOVX *)
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if ((rGPR(rt) == 0) ^ ismovn) then
    writeCapReg(cd) := readCapReg(cb);
  (* END_CMOVX *)
}

union ast member (ClearRegSet, bit[16]) ClearRegs
function clause execute (ClearRegs(regset, mask)) =
{
  (* START_ClearRegs *)
  if ((regset == CLo) | (regset == CHi)) then
    checkCP2usable();
  if (regset == CHi) then
      foreach (i from 0 to 15)
        let r = ((bit[5]) (i+16)) in
        if (mask[i] & register_inaccessible(r)) then
          raise_c2_exception(CapEx_AccessSystemRegsViolation, r);
  foreach (i from 0 to 15)
    if (mask[i]) then
      switch (regset) {
        case GPLo -> wGPR((bit[5])i) := 0
        case GPHi -> wGPR((bit[5])(i+16)) := 0
        case CLo  -> writeCapReg((bit[5]) i) := null_cap
        case CHi  -> writeCapReg((bit[5]) (i+16)) := null_cap
      }
  (* END_ClearRegs *)
}

union ast member regregreg CFromPtr
function clause execute (CFromPtr(cd, cb, rt)) =
{
  (* START_CFromPtr *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  rt_val := rGPR(rt);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (rt == 0) then
    writeCapReg(cd, null_cap)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    let (success, newCap) = setCapOffset(cb_val, rt_val) in
    if (success) then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(getCapBase(cb_val) + rt_val))
  (* END_CFromPtr *)
}

union ast member regregreg CBuildCap
function clause execute (CBuildCap(cd, cb, ct)) =
{
  (* START_CBuildCap *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  ct_val := readCapReg(ct);
  cb_base := getCapBase(cb_val);
  ct_base := getCapBase(ct_val);
  cb_top := getCapTop(cb_val);
  ct_top := getCapTop(ct_val);
  cb_perms := getCapPerms(cb_val);
  ct_perms := getCapPerms(ct_val);
  ct_offset := getCapOffset(ct_val);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ct_base < cb_base then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if ct_top > cb_top then
    raise_c2_exception(CapEx_LengthViolation, cb)
   else if ct_base > ct_top then (* check for length < 0 - possible because ct might be untagged *)
    raise_c2_exception(CapEx_LengthViolation, ct)
   else if (ct_perms & cb_perms) != ct_perms then
    raise_c2_exception(CapEx_UserDefViolation, ct)
  else
    let (exact, cd1) = setCapBounds(cb_val, (bit[64]) ct_base, (bit[65]) ct_top) in 
    let (representable, cd2) = setCapOffset(cd1, (bit[64]) ct_offset) in
    let cd3 = setCapPerms(cd2, ct_perms) in
    {
      assert(exact, None);         (* base and top came from ct originally so will be exact *)
      assert(representable, None); (* similarly offset should be representable XXX except for fastRepCheck *)
      writeCapReg(cd, cd3);
    }
  (* END_CBuildCap *)
}

union ast member regregreg CCopyType
function clause execute (CCopyType(cd, cb, ct)) =
{
  (* START_CCopyType *)
    checkCP2usable();
  cb_val := readCapReg(cb);
  ct_val := readCapReg(ct);
  cb_base := getCapBase(cb_val);
  cb_top  := getCapTop(cb_val);
  ct_otype := unsigned(ct_val.otype);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if (ct_val.sealed) then {
    if ct_otype < cb_base then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else if ct_otype >= cb_top then
      raise_c2_exception(CapEx_LengthViolation, cb)
    else
      let (success, cap) = setCapOffset(cb_val, (bit[64]) (ct_otype - cb_base)) in {
        assert(success, None); (* offset is in bounds so must succeed *)
        writeCapReg(cd, cap);
      }
  } else
    writeCapReg(cd, int_to_cap(-1))
  (* END_CCopyType *)
}

union ast member (regno, regno) CCheckPerm
function clause execute (CCheckPerm(cs, rt)) =
{
  (* START_CCheckPerm *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  cs_perms := EXTZ(getCapPerms(cs_val));
  rt_perms := rGPR(rt);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if ((cs_perms & rt_perms) != rt_perms) then
    raise_c2_exception(CapEx_UserDefViolation, cs)
  else
    ()
  (* END_CCheckPerm *)
}

union ast member (regno, regno) CCheckType
function clause execute (CCheckType(cs, cb)) =
{
  (* START_CCheckType *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if not (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if not (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ((cs_val.otype) != (cb_val.otype)) then
    raise_c2_exception(CapEx_TypeViolation, cs)
  else
    ()
  (* END_CCheckType *)
}

union ast member regregreg CSeal
function clause execute (CSeal(cd, cs, ct)) =
{
  (* START_CSeal *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  ct_val := readCapReg(ct);
  ct_cursor := getCapCursor(ct_val);
  ct_top    := getCapTop(ct_val);
  ct_base   := getCapBase(ct_val);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (ct_val.tag) then
    raise_c2_exception(CapEx_TagViolation, ct)
  else if (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if (ct_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, ct)
  else if not (ct_val.permit_seal) then
    raise_c2_exception(CapEx_PermitSealViolation, ct)
  else if (ct_cursor < ct_base) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if (ct_cursor >= ct_top) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if (ct_cursor > max_otype) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else
    let (success, newCap) = sealCap(cs_val, (bit[24]) ct_cursor) in
    if not (success) then
        raise_c2_exception(CapEx_InexactBounds, cs)
    else
        writeCapReg(cd, newCap)
  (* END_CSeal *)
}

union ast member regregreg CCSeal
function clause execute (CCSeal(cd, cs, ct)) =
{
  (* START_CCSeal *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  ct_val := readCapReg(ct);
  ct_cursor := getCapCursor(ct_val);
  ct_top    := getCapTop(ct_val);
  ct_base   := getCapBase(ct_val);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if (not (ct_val.tag)) | (getCapCursor(ct_val) == -1) then
    writeCapReg(cd, cs_val)
  else if (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if (ct_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, ct)
  else if not (ct_val.permit_seal) then
    raise_c2_exception(CapEx_PermitSealViolation, ct)
  else if (ct_cursor < ct_base) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if (ct_cursor >= ct_top) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if (ct_cursor > max_otype) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else
    let (success, newCap) = sealCap(cs_val, (bit[24]) ct_cursor) in
    if not (success) then
        raise_c2_exception(CapEx_InexactBounds, cs)
    else
        writeCapReg(cd, newCap)
  (* END_CCSeal *)
}

union ast member regregreg CUnseal
function clause execute (CUnseal(cd, cs, ct)) =
{
  (* START_CUnseal *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  ct_val := readCapReg(ct);
  ct_cursor := getCapCursor(ct_val);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (ct_val.tag) then
    raise_c2_exception(CapEx_TagViolation, ct)
  else if not (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if (ct_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, ct)
  else if (ct_cursor != unsigned(cs_val.otype)) then
    raise_c2_exception(CapEx_TypeViolation, ct)
  else if not (ct_val.permit_seal) then
    raise_c2_exception(CapEx_PermitSealViolation, ct)
  else if (ct_cursor <  getCapBase(ct_val)) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else if (ct_cursor >= getCapTop(ct_val)) then
    raise_c2_exception(CapEx_LengthViolation, ct)
  else
    writeCapReg(cd, {cs_val with 
      sealed=false; 
      otype=0;
      global=(cs_val.global & ct_val.global)
    })
  (* END_CUnseal *)
}

union ast member (regno, regno, bit[11]) CCall
function clause execute (CCall(cs, cb, 0b00000000000)) = (* selector=0 *)
{
  (* Partial implementation of CCall with checks in hardware, but raising a trap to perform trusted stack manipulation *)
  (* START_CCall *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  cs_cursor := getCapCursor(cs_val);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if not (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if not (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ((cs_val.otype) != (cb_val.otype)) then
    raise_c2_exception(CapEx_TypeViolation, cs)
  else if not (cs_val.permit_execute) then
    raise_c2_exception(CapEx_PermitExecuteViolation, cs)
  else if (cb_val.permit_execute) then
    raise_c2_exception(CapEx_PermitExecuteViolation, cb)
  else if (cs_cursor < getCapBase(cs_val)) then
    raise_c2_exception(CapEx_LengthViolation, cs)
  else if (cs_cursor >= getCapTop(cs_val)) then
    raise_c2_exception(CapEx_LengthViolation, cs)
  else
    raise_c2_exception(CapEx_CallTrap, cs);
  (* END_CCall *)
}

function clause execute (CCall(cs, cb, 0b00000000001)) = (* selector=1 *)
{
  (* Jump-like implementation of CCall that unseals arguments *)
  (* START_CCall2 *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  cs_cursor := getCapCursor(cs_val);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if not (cs_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cs)
  else if not (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if ((cs_val.otype) != (cb_val.otype)) then
    raise_c2_exception(CapEx_TypeViolation, cs)
  else if not (cs_val.permit_ccall) then
    raise_c2_exception(CapEx_PermitCCallViolation, cs)
  else if not (cb_val.permit_ccall) then
    raise_c2_exception(CapEx_PermitCCallViolation, cb)
  else if not (cs_val.permit_execute) then
    raise_c2_exception(CapEx_PermitExecuteViolation, cs)
  else if (cb_val.permit_execute) then
    raise_c2_exception(CapEx_PermitExecuteViolation, cb)
  else if (cs_cursor < getCapBase(cs_val)) then
    raise_c2_exception(CapEx_LengthViolation, cs)
  else if (cs_cursor >= getCapTop(cs_val)) then
    raise_c2_exception(CapEx_LengthViolation, cs)
  else
    let csUnsealed = capStructToCapReg({cs_val with
        sealed=false;
        otype=0;
    }) in {
      nextPC := (bit[64]) (getCapOffset(cs_val));
      nextPCC := csUnsealed;
      delayedPCC := csUnsealed;
      C26 := capStructToCapReg({cb_val with
        sealed=false;
        otype=0;
      });
    }
  (* END_CCall2 *)
}

union ast member unit CReturn
function clause execute (CReturn) =
{
  (* START_CReturn *)
  checkCP2usable();
  raise_c2_exception_noreg(CapEx_ReturnTrap)
  (* END_CReturn *)
}

union ast member (regno, bit[16], bool) CBX
function clause execute (CBX(cb, imm, invert)) =
{
  (* START_CBx *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (((readCapReg(cb)).tag) ^ invert) then
    {
      let (bit[64]) offset = (EXTS(imm : 0b00) + 4) in
      delayedPC     := PC + offset;
      branchPending := 1;
    }
  (* END_CBx *)
}

union ast member (regno, bit[16], bool) CBZ
function clause execute (CBZ(cb, imm, invert)) =
{
  (* START_CBz *)
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (((readCapReg(cb)) == null_cap) ^ invert) then
    {
      let (bit[64]) offset = (EXTS(imm : 0b00) + 4) in
      delayedPC     := PC + offset;
      branchPending := 1;
    }
  (* END_CBz *)
}

union ast member (regno, regno, bool) CJALR
function clause execute(CJALR(cd, cb, link)) = 
{
  (* START_CJALR *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  cb_ptr := getCapCursor(cb_val);
  cb_top := getCapTop(cb_val);
  cb_base:= getCapBase(cb_val);
  if (link & register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_execute) then
    raise_c2_exception(CapEx_PermitExecuteViolation, cb)
  else if (cb_ptr < cb_base) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if ((cb_ptr + 4) > cb_top) then
    raise_c2_exception(CapEx_LengthViolation, cb)
  else if ((cb_ptr mod 4) != 0) then
    SignalException(AdEL)
  else
    {
      if (link) then
        let pcc = capRegToCapStruct(PCC) in
        let (success, linkCap) = setCapOffset(pcc, PC+8) in
        if (success) then
            writeCapReg(cd, linkCap)
        else
            assert(false, None);
      delayedPC :=  (bit[64]) (getCapOffset(cb_val));
      delayedPCC := capStructToCapReg(cb_val);
      branchPending := 1;
    }
  (* END_CJALR *)
}

union ast member (regno, regno, regno, bit[8], bool, WordType, bool) CLoad
function clause execute (CLoad(rd, cb, rt, offset, signext, width, linked)) =
{
  (* START_CLoad *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_load) then
    raise_c2_exception(CapEx_PermitLoadViolation, cb)
  else
    {
      size   := wordWidthBytes(width);
      cursor := getCapCursor(cb_val);
      vAddr  := cursor + unsigned(rGPR(rt)) + (size*signed(offset));
      vAddr64:= (bit[64]) vAddr;
      if ((vAddr + size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if not (isAddressAligned(vAddr64, width)) then
        SignalExceptionBadAddr(AdEL, vAddr64)
      else
        {
          pAddr      := (TLBTranslate(vAddr64, LoadData));
          widthBytes := wordWidthBytes(width);
          memResult  := if (linked) then
              {
                CP0LLBit  := 0b1;
                CP0LLAddr := pAddr;
                MEMr_reserve_wrapper(pAddr, widthBytes);
              }
            else
              MEMr_wrapper(pAddr, widthBytes);
          if (signext) then
            wGPR(rd) := EXTS(memResult)
          else
            wGPR(rd) := EXTZ(memResult)
        }
    }
  (* END_CLoad *)
}

union ast member (regno, regno, regno, regno, bit[8], WordType, bool) CStore

function clause execute (CStore(rs, cb, rt, rd, offset, width, conditional)) =
{
  (* START_CStore *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_store) then
    raise_c2_exception(CapEx_PermitStoreViolation, cb)
  else
    {
      size   := wordWidthBytes(width);
      cursor := getCapCursor(cb_val);
      vAddr  := cursor + unsigned(rGPR(rt)) + (size * signed(offset));
      vAddr64:= (bit[64]) vAddr;
      if ((vAddr + size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if not (isAddressAligned(vAddr64, width)) then
        SignalExceptionBadAddr(AdES, vAddr64)
      else
        {
          pAddr  := (TLBTranslate(vAddr64, StoreData));
          rs_val := rGPR(rs);
          if (conditional) then
            {
              success := if (CP0LLBit[0]) then
                  switch(width)
                    {
                      case B -> MEMw_conditional_wrapper(pAddr, 1, rs_val[7..0])
                      case H -> MEMw_conditional_wrapper(pAddr, 2, rs_val[15..0])
                      case W -> MEMw_conditional_wrapper(pAddr, 4, rs_val[31..0])
                      case D -> MEMw_conditional_wrapper(pAddr, 8, rs_val)
                    }
                else
                  false;
              wGPR(rd) := EXTZ([success]);
            }
            else
          switch(width)
            {
              case B -> MEMw_wrapper(pAddr, 1) := rs_val[7..0]
              case H -> MEMw_wrapper(pAddr, 2) := rs_val[15..0]
              case W -> MEMw_wrapper(pAddr, 4) := rs_val[31..0]
              case D -> MEMw_wrapper(pAddr, 8) := rs_val
            }
        }
    }
  (* END_CStore *)
}

union ast member (regno, regno, regno, regno, bit[11], bool) CSC
function clause execute (CSC(cs, cb, rt, rd, offset, conditional)) =
{
  (* START_CSC *)
  checkCP2usable();
  cs_val := readCapReg(cs);
  cb_val := readCapReg(cb);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_store_cap) then
    raise_c2_exception(CapEx_PermitStoreCapViolation, cb)
  else if not (cb_val.permit_store_local_cap) & (cs_val.tag) & not (cs_val.global) then
    raise_c2_exception(CapEx_PermitStoreLocalCapViolation, cb)
  else
    {
      cursor := getCapCursor(cb_val);
      vAddr  := cursor + unsigned(rGPR(rt)) + (16 * signed(offset));
      vAddr64:= (bit[64]) vAddr;
      if ((vAddr + cap_size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if ((vAddr mod cap_size) != 0) then
        SignalExceptionBadAddr(AdES, vAddr64)
      else
        {
          let (pAddr, noStoreCap)  = (TLBTranslateC(vAddr64, StoreData)) in
          if (cs_val.tag & noStoreCap) then
            raise_c2_exception(CapEx_TLBNoStoreCap, cs)
          else if (conditional) then
            {
              success := if (CP0LLBit[0]) then
                  MEMw_tagged_conditional(pAddr, cs_val.tag, capStructToMemBits(cs_val))
                else
                  false;
              wGPR(rd) := EXTZ([success]);
            }
          else
            MEMw_tagged(pAddr, cs_val.tag, capStructToMemBits(cs_val));
        }
    }
  (* END_CSC *)
}

union ast member (regno, regno, regno, bit[11], bool) CLC
function clause execute (CLC(cd, cb, rt, offset, linked)) =  
{
  (* START_CLC *)
  checkCP2usable();
  cb_val := readCapReg(cb);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    {
      cursor := getCapCursor(cb_val);
      vAddr  := cursor + unsigned(rGPR(rt)) + (16*signed(offset));
      vAddr64:= (bit[64]) vAddr;
      if ((vAddr + cap_size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if ((vAddr mod cap_size) != 0) then
        SignalExceptionBadAddr(AdEL, vAddr64)
      else
        {
          let (pAddr, suppressTag) = (TLBTranslateC(vAddr64, LoadData)) in
          let (tag, mem) = (if (linked) 
            then
              {
                CP0LLBit  := 0b1;
                CP0LLAddr := pAddr;
                MEMr_tagged_reserve(pAddr);
              }
            else 
              (MEMr_tagged(pAddr)))
          in
          (CapRegs[cd]) := memBitsToCapBits(tag & (cb_val.permit_load_cap) & not (suppressTag), mem);
        }
    }
  (* END_CLC *)
}

union ast member (regno) C2Dump
function clause execute (C2Dump (rt)) =
    () (* Currently a NOP *)
