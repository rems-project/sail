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

/* Old encodings */
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b000) = Some(CGetPerm(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b001) = Some(CGetType(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b010) = Some(CGetBase(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b011) = Some(CGetLen(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b101) = Some(CGetTag(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ 0b00000000 @ 0b110) = Some(CGetSealed(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @    0b00000 @ 0b00000000 @ 0b100) = Some(CGetCause(rd))

function clause decode (0b010010 @ 0b00110 @ 0b000000000000000000000) = Some(CReturn)

function clause decode (0b010010 @ 0b01101 @ rd : regno @ cb : regno @ 0b00000000 @ 0b010) = Some(CGetOffset(rd, cb)) /* NB encoding does not follow pattern */
function clause decode (0b010010 @ 0b00100 @ 0b00000 @ 0b00000 @ rt : regno @ 0b000 @ 0b100) = Some(CSetCause(rt))
function clause decode (0b010010 @ 0b00100 @ cd : regno @ cb : regno @ rt : regno @ 0b000 @ 0b000) = Some(CAndPerm(cd, cb, rt))
function clause decode (0b010010 @ 0b01100 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b000) = Some(CToPtr(rd, cb, ct))

function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b000) = Some(CPtrCmp(rd, cb, ct, CEQ))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b001) = Some(CPtrCmp(rd, cb, ct, CNE))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b010) = Some(CPtrCmp(rd, cb, ct, CLT))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b011) = Some(CPtrCmp(rd, cb, ct, CLE))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b100) = Some(CPtrCmp(rd, cb, ct, CLTU))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b101) = Some(CPtrCmp(rd, cb, ct, CLEU))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b110) = Some(CPtrCmp(rd, cb, ct, CEXEQ))
function clause decode (0b010010 @ 0b01110 @ rd : regno @ cb : regno @ ct : regno @ 0b000 @ 0b111) = Some(CPtrCmp(rd, cb, ct, CNEXEQ))
function clause decode (0b010010 @ 0b01101 @ cd : regno @ cb : regno @ rt : regno @ 0b000 @ 0b000) = Some(CIncOffset(cd, cb, rt))
function clause decode (0b010010 @ 0b01101 @ cd : regno @ cb : regno @ rt : regno @ 0b000 @ 0b001) = Some(CSetOffset(cd, cb, rt))
function clause decode (0b010010 @ 0b00001 @ cd : regno @ cb : regno @ rt : regno @ 0b000000)      = Some(CSetBounds(cd, cb, rt))

function clause decode (0b010010 @ 0b00100 @ cd : regno @ cb : regno @ 0b00000 @ 0b000@ 0b101)    = Some(CClearTag(cd, cb))
function clause decode (0b010010 @ 0b00100 @ cd : regno @ cb : regno @ rt : regno @ 0b000@ 0b111) = Some(CFromPtr(cd, cb, rt))
function clause decode (0b010010 @ 0b01011 @ cs : regno @ 0b00000 @ rt : regno @ 0b000@ 0b000) = Some(CCheckPerm(cs, rt))
function clause decode (0b010010 @ 0b01011 @ cs : regno @ cb : regno @ 0b00000 @ 0b000@ 0b001) = Some(CCheckType(cs, cb))
function clause decode (0b010010 @ 0b00010 @ cd : regno @ cs : regno @ ct : regno @ 0b000@ 0b000) = Some(CSeal(cd, cs, ct))
function clause decode (0b010010 @ 0b00011 @ cd : regno @ cs : regno @ ct : regno @ 0b000@ 0b000) = Some(CUnseal(cd, cs, ct))
function clause decode (0b010010 @ 0b00111 @ cd : regno @ cb : regno @ 0b00000 @ 0b000000) = Some(CJALR(cd, cb, true)) /* CJALR */
function clause decode (0b010010 @ 0b01000 @ 0b00000    @ cb : regno @ 0b00000 @ 0b000000) = Some(CJALR(0b00000, cb, false)) /* CJR */


/* 
New encodings as per CHERI ISA Appendix B.2.  

NB: Must be careful about order of matching because unused register
fields are re-used as additional function codes.
*/

/* One arg */
function clause decode (0b010010 @ 0b00000 @ rd : regno @    0b00001 @    0b11111 @ 0b111111) = Some(CGetCause(rd))
function clause decode (0b010010 @ 0b00000 @ rs : regno @    0b00010 @    0b11111 @ 0b111111) = Some(CSetCause(rs))
function clause decode (0b010010 @ 0b00000 @ cd : regno @    0b00000 @    0b11111 @ 0b111111) = Some(CGetPCC(cd))
function clause decode (0b010010 @ 0b00000 @ cb : regno @    0b00011 @    0b11111 @ 0b111111) = Some(CJALR(0b00000, cb, false)) /* CJR */

/* Two arg */
function clause decode (0b010010 @ 0b00000 @ cs : regno @ rt : regno @    0b01000 @ 0b111111) = Some(CCheckPerm(cs, rt))
function clause decode (0b010010 @ 0b00000 @ cs : regno @ cb : regno @    0b01001 @ 0b111111) = Some(CCheckType(cs, cb))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @    0b01011 @ 0b111111) = Some(CClearTag(cd, cb))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @    0b01010 @ 0b111111) = Some(CMOVX(cd, cs, 0b00000, false)) /* CMOVE */
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @    0b01100 @ 0b111111) = Some(CJALR(cd, cb, true)) /* CJALR */

/* Capability Inspection */
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00000 @ 0b111111) = Some(CGetPerm(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00001 @ 0b111111) = Some(CGetType(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00010 @ 0b111111) = Some(CGetBase(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00011 @ 0b111111) = Some(CGetLen(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00100 @ 0b111111) = Some(CGetTag(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00101 @ 0b111111) = Some(CGetSealed(rd, cb))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @    0b00110 @ 0b111111) = Some(CGetOffset(rd, cb))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ rs : regno @    0b00111 @ 0b111111) = Some(CGetPCCSetOffset(cd, rs))

/* Three operand */

/* Capability Modification */
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ ct : regno @ 0b001011) = Some(CSeal(cd, cs, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ ct : regno @ 0b001100) = Some(CUnseal(cd, cs, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rt : regno @ 0b001101) = Some(CAndPerm(cd, cs, rt))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rt : regno @ 0b001111) = Some(CSetOffset(cd, cs, rt))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rt : regno @ 0b001000) = Some(CSetBounds(cd, cs, rt))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rt : regno @ 0b001001) = Some(CSetBoundsExact(cd, cs, rt))


function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ rt : regno @ 0b010001) = Some(CIncOffset(cd, cb, rt))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ ct : regno @ 0b011101) = Some(CBuildCap(cd, cb, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ ct : regno @ 0b011110) = Some(CCopyType(cd, cb, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ ct : regno @ 0b011111) = Some(CCSeal(cd, cs, ct))

/* Pointer Arithmetic */
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ ct : regno @ 0b010010) = Some(CToPtr(rd, cb, ct))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cb : regno @ rs : regno @ 0b010011) = Some(CFromPtr(cd, cb, rs))
function clause decode (0b010010 @ 0b00000 @ rt : regno @ cb : regno @ cs : regno @ 0b001010) = Some(CSub(rt, cb, cs))
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rs : regno @ 0b011011) = Some(CMOVX(cd, cs, rs, false)) /* CMOVZ */
function clause decode (0b010010 @ 0b00000 @ cd : regno @ cs : regno @ rs : regno @ 0b011100) = Some(CMOVX(cd, cs, rs, true))  /* CMOVN */

/* Pointer Comparison */
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b010100) = Some(CPtrCmp(rd, cb, cs, CEQ))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b010101) = Some(CPtrCmp(rd, cb, cs, CNE))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b010110) = Some(CPtrCmp(rd, cb, cs, CLT))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b010111) = Some(CPtrCmp(rd, cb, cs, CLE))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b011000) = Some(CPtrCmp(rd, cb, cs, CLTU))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b011001) = Some(CPtrCmp(rd, cb, cs, CLEU))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b011010) = Some(CPtrCmp(rd, cb, cs, CEXEQ))
function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ cs : regno @ 0b100001) = Some(CPtrCmp(rd, cb, cs, CNEXEQ))

function clause decode (0b010010 @ 0b00000 @ rd : regno @ cb : regno @ ct : regno @ 0b100000) = Some(CTestSubset(rd, cb, ct))

function clause decode (0b010010 @ 0b01001 @ cd : regno @ imm : bits(16)) = Some(CBX(cd, imm, true))  /* CBTU */
function clause decode (0b010010 @ 0b01010 @ cd : regno @ imm : bits(16)) = Some(CBX(cd, imm, false)) /* CBTS */
function clause decode (0b010010 @ 0b10001 @ cd : regno @ imm : bits(16)) = Some(CBZ(cd, imm, false)) /* CBEZ */
function clause decode (0b010010 @ 0b10010 @ cd : regno @ imm : bits(16)) = Some(CBZ(cd, imm, true))  /* CBNZ */

function clause decode (0b010010 @ 0b00101 @    0b00000 @    0b00000 @ 0b11111111111) = Some(CReturn)
function clause decode (0b010010 @ 0b00101 @ cs : regno @ cb : regno @ selector : bits(11)) = Some(CCall(cs, cb, selector))

function clause decode (0b010010 @ 0b01111 @ 0b00000 @ imm : bits(16)) = Some(ClearRegs(GPLo, imm))
function clause decode (0b010010 @ 0b01111 @ 0b00001 @ imm : bits(16)) = Some(ClearRegs(GPHi, imm))
function clause decode (0b010010 @ 0b01111 @ 0b00010 @ imm : bits(16)) = Some(ClearRegs(CLo,  imm))
function clause decode (0b010010 @ 0b01111 @ 0b00011 @ imm : bits(16)) = Some(ClearRegs(CHi,  imm))

function clause decode (0b010010 @ 0b10011 @ cd : regno @ cb : regno @ imm : bits(11)) = Some(CIncOffsetImmediate(cd, cb, imm))
function clause decode (0b010010 @ 0b10100 @ cd : regno @ cb : regno @ imm : bits(11)) = Some(CSetBoundsImmediate(cd, cb, imm))

function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b00) = Some(CLoad(rd, cb, rt, offset, false, B, false)) /* CLBU */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b1 @ 0b00) = Some(CLoad(rd, cb, rt, offset, true,  B, false)) /* CLB */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b01) = Some(CLoad(rd, cb, rt, offset, false, H, false)) /* CLHU */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b1 @ 0b01) = Some(CLoad(rd, cb, rt, offset, true,  H, false)) /* CLH */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b10) = Some(CLoad(rd, cb, rt, offset, false, W, false)) /* CLWU */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b1 @ 0b10) = Some(CLoad(rd, cb, rt, offset, true,  W, false)) /* CLW */
function clause decode (0b110010 @ rd : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b11) = Some(CLoad(rd, cb, rt, offset, false, D, false)) /* CLD */

function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b0 @ 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, B, true)) /* CLLBU */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b1 @ 0b00) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  B, true)) /* CLLB  */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b0 @ 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, H, true)) /* CLLHU */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b1 @ 0b01) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  H, true)) /* CLLH  */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b0 @ 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, W, true)) /* CLLWU */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b1 @ 0b10) = Some(CLoad(rd, cb, 0b00000, 0b00000000, true,  W, true)) /* CLLW  */
function clause decode (0b010010 @ 0b10000 @ rd : regno @ cb : regno @ 0b00000001 @ 0b0 @ 0b11) = Some(CLoad(rd, cb, 0b00000, 0b00000000, false, D, true)) /* CLLD  */

function clause decode (0b111010 @ rs : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b00) = Some(CStore(rs, cb, rt, 0b00000, offset, B, false)) /* CSB */
function clause decode (0b111010 @ rs : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b01) = Some(CStore(rs, cb, rt, 0b00000, offset, H, false)) /* CSH */
function clause decode (0b111010 @ rs : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b10) = Some(CStore(rs, cb, rt, 0b00000, offset, W, false)) /* CSW */
function clause decode (0b111010 @ rs : regno @ cb : regno@ rt : regno @ offset : bits(8) @ 0b0 @ 0b11) = Some(CStore(rs, cb, rt, 0b00000, offset, D, false)) /* CSD */

function clause decode (0b010010 @ 0b10000 @ rs : regno @ cb : regno @ rd : regno @ 0b0000 @ 0b00) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, B, true)) /* CSCB */
function clause decode (0b010010 @ 0b10000 @ rs : regno @ cb : regno @ rd : regno @ 0b0000 @ 0b01) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, H, true)) /* CSCH */
function clause decode (0b010010 @ 0b10000 @ rs : regno @ cb : regno @ rd : regno @ 0b0000 @ 0b10) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, W, true)) /* CSCW */
function clause decode (0b010010 @ 0b10000 @ rs : regno @ cb : regno @ rd : regno @ 0b0000 @ 0b11) = Some(CStore(rs, cb, 0b00000, rd, 0b00000000, D, true)) /* CSCD */

function clause decode (0b111110 @ cs : regno @ cb : regno@ rt : regno @ offset : bits(11)) = Some(CSC(cs, cb, rt, 0b00000, offset, false))
function clause decode (0b010010 @ 0b10000 @ cs : regno @ cb : regno@ rd : regno @ 0b00 @ 0b0111) = Some(CSC(cs, cb, 0b00000, rd, 0b00000000000, true))

function clause decode (0b110110 @ cd : regno @ cb : regno@ rt : regno @ offset : bits(11)) = Some(CLC(cd, cb, rt, offset, false))
function clause decode (0b010010 @ 0b10000 @ cd : regno @ cb : regno@ 0b0000000 @ 0b1111) = Some(CLC(cd, cb, 0b00000, 0b00000000000, true))

function clause decode (0b010010 @ 0b00100 @ rt : regno @ 0x0006) = Some(C2Dump(rt))

/* Operations that extract parts of a capability into GPR */

union clause ast = CGetPerm   : (regno, regno)
union clause ast = CGetType   : (regno, regno)
union clause ast = CGetBase   : (regno, regno)
union clause ast = CGetLen    : (regno, regno)
union clause ast = CGetTag    : (regno, regno)
union clause ast = CGetSealed : (regno, regno)
union clause ast = CGetOffset : (regno, regno)

function clause execute (CGetPerm(rd, cb)) =
{
  /* START_CGetPerms */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = EXTZ(getCapPerms(capVal));
  /* END_CGetPerms */
}

function clause execute (CGetType(rd, cb)) =
{
  /* START_CGetType */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = if (capVal.sealed)
      then EXTZ(capVal.otype)
      else (bitone ^^ 64)
  /* END_CGetType */
}

function clause execute (CGetBase(rd, cb)) =
{
  /* START_CGetBase */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = to_bits(64, getCapBase(capVal));
  /* END_CGetBase */
}

function clause execute (CGetOffset(rd, cb)) =
{
  /* START_CGetOffset */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = to_bits(64, getCapOffset(capVal));
  /* END_CGetOffset */
}

function clause execute (CGetLen(rd, cb)) =
{
  /* START_CGetLen */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    let len65  = getCapLength(capVal) in
    wGPR(rd) = to_bits(64, if len65 > MAX_U64 then MAX_U64 else len65);
  /* END_CGetLen */
}

function clause execute (CGetTag(rd, cb)) =
{
  /* START_CGetTag */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = EXTZ(capVal.tag);
  /* END_CGetTag */
}

function clause execute (CGetSealed(rd, cb)) =
{
  /* START_CGetSealed */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    let capVal = readCapReg(cb) in
    wGPR(rd) = EXTZ(capVal.sealed);
  /* END_CGetSealed */
}

union clause ast = CGetPCC : regno
function clause execute (CGetPCC(cd)) =
{
  /* START_CGetPCC */
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else
    let pcc = (capRegToCapStruct(PCC)) in
    let (success, pcc2) = setCapOffset(pcc, PC) in
    {assert (success, ""); /* guaranteed to be in-bounds */
    writeCapReg(cd, pcc2)};
  /* END_CGetPCC */
}


union clause ast = CGetPCCSetOffset : (regno, regno)
function clause execute (CGetPCCSetOffset(cd, rs)) =
{
  /* START_CGetPCCSetOffset */
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
  /* END_CGetPCCSetOffset */
}
/* Get and Set CP2 cause register */

union clause ast = CGetCause : regno
function clause execute (CGetCause(rd)) = 
{
  /* START_CGetCause */
  checkCP2usable();
  if not (pcc_access_system_regs ()) then
    raise_c2_exception_noreg(CapEx_AccessSystemRegsViolation)
  else
    wGPR(rd) = EXTZ(CapCause.bits())
  /* END_CGetCause */
}

union clause ast = CSetCause : regno
function clause execute (CSetCause(rt)) = 
{
  /* START_CSetCause */
  checkCP2usable();
  if not (pcc_access_system_regs ()) then
    raise_c2_exception_noreg(CapEx_AccessSystemRegsViolation)
  else
    {
      let rt_val = rGPR(rt);
      CapCause->ExcCode() = rt_val[15..8];
      CapCause->RegNum()  = rt_val[7..0];
    }
  /* END_CSetCause */
}

union clause ast = CAndPerm : (regno, regno, regno)
function clause execute(CAndPerm(cd, cb, rt)) = 
{
  /* START_CAndPerm */
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let rt_val = rGPR(rt);
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
  /* END_CAndPerm */
}



union clause ast = CToPtr : (regno, regno, regno)
function clause execute(CToPtr(rd, cb, ct)) = 
{
  /* START_CToPtr */
  checkCP2usable();
  let ct_val = readCapReg(ct);
  let cb_val = readCapReg(cb);
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
      wGPR(rd) = if (not (cb_val.tag)) |
                     (cbBase < ctBase) |
                     (cbTop > ctTop) then
          zeros()
        else
          to_bits(64, getCapCursor(cb_val) - ctBase)
    }
  /* END_CToPtr */
}



union clause ast = CSub : (regno, regno, regno)
function clause execute(CSub(rd, cb, ct)) = 
{
  /* START_CSub */
  checkCP2usable();
  let ct_val = readCapReg(ct);
  let cb_val = readCapReg(cb);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else 
    {
      wGPR(rd) = to_bits(64, getCapCursor(cb_val) - getCapCursor(ct_val))
    }
  /* END_CSub */
}

union clause ast = CPtrCmp : (regno, regno, regno, CPtrCmpOp)
function clause execute(CPtrCmp(rd, cb, ct, op)) = 
{
  /* START_CPtrCmp */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else 
    {
      let cb_val = readCapReg(cb);
      let ct_val = readCapReg(ct);
      equal  = false;
      ltu    = false;
      lts    = false;
      if (cb_val.tag != ct_val.tag) then
        {
          if not (cb_val.tag) then
            {
              ltu = true;
              lts = true;
            }
        }
      else
        {
          cursor1 = getCapCursor(cb_val);
          cursor2 = getCapCursor(ct_val);
          equal   = (cursor1 == cursor2);
          ltu     = (cursor1 < cursor2);
          lts     = to_bits(64, cursor1) <_s to_bits(64, cursor2);
        };
      let cmp : bool = match op {
        CEQ    => equal,
        CNE    => not (equal),
        CLT    => lts,
        CLE    => lts | equal,
        CLTU   => ltu,
        CLEU   => ltu | equal,
        CEXEQ  => cb_val == ct_val,
        CNEXEQ => cb_val != ct_val
      };
      wGPR(rd) = EXTZ (cmp)
    }
  /* END_CPtrCmp */
}

union clause ast = CIncOffset : (regno, regno, regno)
function clause execute (CIncOffset(cd, cb, rt)) =
{
  /* START_CIncOffset */
  checkCP2usable();
  cb_val = readCapReg(cb);
  rt_val = rGPR(rt);
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
        writeCapReg(cd, int_to_cap(to_bits(64, getCapBase(cb_val)) + rt_val))
  /* END_CIncOffset */
}

union clause ast = CIncOffsetImmediate : (regno, regno, bits(11))
function clause execute (CIncOffsetImmediate(cd, cb, imm)) =
{
  /* START_CIncOffsetImmediate */
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let imm64 : bits(64) = EXTS(imm) in
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if ((cb_val.tag) & (cb_val.sealed)) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else
    let (success, newCap) = incCapOffset(cb_val, imm64) in
    if (success) then
        writeCapReg(cd, newCap)
    else
        writeCapReg(cd, int_to_cap(to_bits(64, getCapBase(cb_val)) + imm64))
  /* END_CIncOffsetImmediate */
}

union clause ast = CSetOffset : (regno, regno, regno)
function clause execute (CSetOffset(cd, cb, rt)) =
{
  /* START_CSetOffset */
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let rt_val = rGPR(rt);
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
        writeCapReg(cd, int_to_cap(to_bits(64, getCapBase(cb_val)) + rt_val))
  /* END_CSetOffset */
}

union clause ast = CSetBounds : (regno, regno, regno)
function clause execute (CSetBounds(cd, cb, rt)) =
{
  /* START_CSetBounds */
  checkCP2usable();
  let cb_val = readCapReg(cb);
  let rt_val = unsigned(rGPR(rt));
  cursor = getCapCursor(cb_val);
  base   = getCapBase(cb_val);
  top    = getCapTop(cb_val);
  newTop = cursor + rt_val;
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
    let (_, newCap) = setCapBounds(cb_val, to_bits(64, cursor), to_bits(65, newTop)) in
    writeCapReg(cd, newCap) /* ignore exact */
  /* END_CSetBounds */
}

union clause ast = CSetBoundsImmediate : (regno, regno, bits(11))
function clause execute (CSetBoundsImmediate(cd, cb, imm)) =
{
  /* START_CSetBoundsImmedate */
  checkCP2usable();
  cb_val = readCapReg(cb);
  immU   = unsigned(imm);
  cursor = getCapCursor(cb_val);
  base   = getCapBase(cb_val);
  top    = getCapTop(cb_val);
  newTop = cursor + immU;
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
    let (_, newCap) = setCapBounds(cb_val, to_bits(64, cursor), to_bits(65, newTop)) in
    writeCapReg(cd, newCap) /* ignore exact */
  /* END_CSetBoundsImmediate */
}

union clause ast = CSetBoundsExact : (regno, regno, regno)
function clause execute (CSetBoundsExact(cd, cb, rt)) =
{
  /* START_CSetBoundsExact */
  checkCP2usable();
  cb_val = readCapReg(cb);
  rt_val = unsigned(rGPR(rt));
  cursor = getCapCursor(cb_val);
  base   = getCapBase(cb_val);
  top    = getCapTop(cb_val);
  newTop = cursor + rt_val;
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
    let (exact, newCap) = setCapBounds(cb_val, to_bits(64, cursor), to_bits(65, newTop)) in
    if not (exact) then
        raise_c2_exception(CapEx_InexactBounds, cb)
    else
        writeCapReg(cd, newCap)
  /* END_CSetBoundsExact */
}

union clause ast = CClearTag : (regno, regno)
function clause execute (CClearTag(cd, cb)) =
{
  /* START_CClearTag */
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else
    {
      cb_val = readCapReg(cb);
      writeCapReg(cd, {cb_val with tag=false});
    }
  /* END_CClearTag */
}

union clause ast = CMOVX : (regno,regno,regno,bool)
function clause execute (CMOVX(cd, cb, rt, ismovn)) =
{
  /* START_CMOVX */
  checkCP2usable();
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if ((rGPR(rt) == zeros()) ^ ismovn) then
    writeCapReg(cd) = readCapReg(cb);
  /* END_CMOVX */
}

union clause ast = ClearRegs : (ClearRegSet, bits(16))
function clause execute (ClearRegs(regset, m)) =
{
  /* START_ClearRegs */
  if ((regset == CLo) | (regset == CHi)) then
    checkCP2usable();
  if (regset == CHi) then
      foreach (i from 0 to 15)
        let r = to_bits(5, i+16) in
        if (m[i] & register_inaccessible(r)) then
          raise_c2_exception(CapEx_AccessSystemRegsViolation, r);
  foreach (i from 0 to 15)
    if (m[i]) then
      match regset {
        GPLo  => wGPR(to_bits(5, i)) = zeros(),
        GPHi  => wGPR(to_bits(5, i+16)) = zeros(),
        CLo   => writeCapReg(to_bits(5, i)) = null_cap,
        CHi   => writeCapReg(to_bits(5, i+16)) = null_cap
      }
  /* END_ClearRegs */
}

union clause ast = CFromPtr : (regno, regno, regno)
function clause execute (CFromPtr(cd, cb, rt)) =
{
  /* START_CFromPtr */
  checkCP2usable();
  cb_val = readCapReg(cb);
  rt_val = rGPR(rt);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (rt == 0b00000) then
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
        writeCapReg(cd, int_to_cap(to_bits(64, getCapBase(cb_val)) + rt_val))
  /* END_CFromPtr */
}

union clause ast = CBuildCap : (regno, regno, regno)
function clause execute (CBuildCap(cd, cb, ct)) =
{
  /* START_CBuildCap */
  checkCP2usable();
  cb_val = readCapReg(cb);
  ct_val = readCapReg(ct);
  cb_base = getCapBase(cb_val);
  ct_base = getCapBase(ct_val);
  cb_top = getCapTop(cb_val);
  ct_top = getCapTop(ct_val);
  cb_perms = getCapPerms(cb_val);
  ct_perms = getCapPerms(ct_val);
  ct_offset = getCapOffset(ct_val);
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
   else if ct_base > ct_top then /* check for length < 0 - possible because ct might be untagged */
    raise_c2_exception(CapEx_LengthViolation, ct)
   else if (ct_perms & cb_perms) != ct_perms then
    raise_c2_exception(CapEx_UserDefViolation, ct)
  else
    let (exact, cd1) = setCapBounds(cb_val, to_bits(64, ct_base), to_bits(65, ct_top)) in 
    let (representable, cd2) = setCapOffset(cd1, to_bits(64, ct_offset)) in
    let cd3 = setCapPerms(cd2, ct_perms) in
    {
      assert(exact, "");         /* base and top came from ct originally so will be exact */
      assert(representable, ""); /* similarly offset should be representable XXX except for fastRepCheck */
      writeCapReg(cd, cd3);
    }
  /* END_CBuildCap */
}

union clause ast = CCopyType : (regno, regno, regno)
function clause execute (CCopyType(cd, cb, ct)) =
{
  /* START_CCopyType */
    checkCP2usable();
  cb_val = readCapReg(cb);
  ct_val = readCapReg(ct);
  cb_base = getCapBase(cb_val);
  cb_top  = getCapTop(cb_val);
  ct_otype = unsigned(ct_val.otype);
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
      let (success, cap) = setCapOffset(cb_val, to_bits(64, ct_otype - cb_base)) in {
        assert(success, ""); /* offset is in bounds so must succeed */
        writeCapReg(cd, cap);
      }
  } else
    writeCapReg(cd, int_to_cap(bitone ^^ 64))
  /* END_CCopyType */
}

union clause ast = CCheckPerm : (regno, regno)
function clause execute (CCheckPerm(cs, rt)) =
{
  /* START_CCheckPerm */
  checkCP2usable();
  cs_val = readCapReg(cs);
  cs_perms : bits(64) = EXTZ(getCapPerms(cs_val));
  rt_perms = rGPR(rt);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if ((cs_perms & rt_perms) != rt_perms) then
    raise_c2_exception(CapEx_UserDefViolation, cs)
  else
    ()
  /* END_CCheckPerm */
}

union clause ast = CCheckType : (regno, regno)
function clause execute (CCheckType(cs, cb)) =
{
  /* START_CCheckType */
  checkCP2usable();
  cs_val = readCapReg(cs);
  cb_val = readCapReg(cb);
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
  /* END_CCheckType */
}

union clause ast = CTestSubset : (regno, regno, regno)
function clause execute (CTestSubset(rd, cb, ct)) =
{
  /* START_CTestSubset */
  checkCP2usable();
  cb_val = readCapReg(cb);
  ct_val = readCapReg(ct);
  ct_top    = getCapTop(ct_val);
  ct_base   = getCapBase(ct_val);
  ct_perms  = getCapPerms(ct_val);
  cb_top    = getCapTop(cb_val);
  cb_base   = getCapBase(cb_val);
  cb_perms  = getCapPerms(cb_val);
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else {
     result : bits(1) = if (cb_val.tag != ct_val.tag) then
             0b0
        else if (cb_val.sealed != ct_val.sealed) then
             0b0
        else if (ct_base < cb_base) then
             0b0
        else if (ct_top > cb_top) then
             0b0
        else if ((ct_perms & cb_perms) != cb_perms) then
             0b0
        else
             0b1;
     wGPR(rd) = EXTZ(result);
  }
  /* END_CTestSubset */
}

union clause ast = CSeal : (regno, regno, regno)
function clause execute (CSeal(cd, cs, ct)) =
{
  /* START_CSeal */
  checkCP2usable();
  cs_val = readCapReg(cs);
  ct_val = readCapReg(ct);
  ct_cursor = getCapCursor(ct_val);
  ct_top    = getCapTop(ct_val);
  ct_base   = getCapBase(ct_val);
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
    let (success, newCap) = sealCap(cs_val, to_bits(24, ct_cursor)) in
    if not (success) then
        raise_c2_exception(CapEx_InexactBounds, cs)
    else
        writeCapReg(cd, newCap)
  /* END_CSeal */
}

union clause ast = CCSeal : (regno, regno, regno)
function clause execute (CCSeal(cd, cs, ct)) =
{
  /* START_CCSeal */
  checkCP2usable();
  cs_val = readCapReg(cs);
  ct_val = readCapReg(ct);
  ct_cursor = getCapCursor(ct_val);
  ct_top    = getCapTop(ct_val);
  ct_base   = getCapBase(ct_val);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(ct)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, ct)
  else if not (cs_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cs)
  else if (not (ct_val.tag)) | (getCapCursor(ct_val) == unsigned(bitone ^^ 64)) then
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
    let (success, newCap) = sealCap(cs_val, to_bits(24, ct_cursor)) in
    if not (success) then
        raise_c2_exception(CapEx_InexactBounds, cs)
    else
        writeCapReg(cd, newCap)
  /* END_CCSeal */
}

union clause ast = CUnseal : (regno, regno, regno)
function clause execute (CUnseal(cd, cs, ct)) =
{
  /* START_CUnseal */
  checkCP2usable();
  cs_val = readCapReg(cs);
  ct_val = readCapReg(ct);
  ct_cursor = getCapCursor(ct_val);
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
      sealed=false,
      otype=zeros(),
      global=(cs_val.global & ct_val.global)
    })
  /* END_CUnseal */
}

union clause ast = CCall : (regno, regno, bits(11))
function clause execute (CCall(cs, cb, 0b00000000000)) = /* selector=0 */
{
  /* Partial implementation of CCall with checks in hardware, but raising a trap to perform trusted stack manipulation */
  /* START_CCall */
  checkCP2usable();
  cs_val = readCapReg(cs);
  cb_val = readCapReg(cb);
  cs_cursor = getCapCursor(cs_val);
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
  /* END_CCall */
}

function clause execute (CCall(cs, cb, 0b00000000001)) = /* selector=1 */
{
  /* Jump-like implementation of CCall that unseals arguments */
  /* START_CCall2 */
  checkCP2usable();
  cs_val = readCapReg(cs);
  cb_val = readCapReg(cb);
  cs_cursor = getCapCursor(cs_val);
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
        sealed=false,
        otype=zeros()
    }) in {
      delayedPC = to_bits(64, getCapOffset(cs_val));
      delayedPCC = csUnsealed;
      branchPending = 0b1;
      inCCallDelay  = 0b1;
      C26 = capStructToCapReg({cb_val with
        sealed=false,
        otype=zeros()
      });
    }
  /* END_CCall2 */
}

union clause ast = CReturn : unit
function clause execute (CReturn) =
{
  /* START_CReturn */
  checkCP2usable();
  raise_c2_exception_noreg(CapEx_ReturnTrap)
  /* END_CReturn */
}

union clause ast = CBX : (regno, bits(16), bool)
function clause execute (CBX(cb, imm, invert)) =
{
  /* START_CBx */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (((readCapReg(cb)).tag) ^ invert) then
    {
      let offset : bits(64) = (EXTS(imm @ 0b00) + 4) in
      delayedPC     = PC + offset;
      branchPending = 0b1;
    }
  /* END_CBx */
}

union clause ast = CBZ : (regno, bits(16), bool)
function clause execute (CBZ(cb, imm, invert)) =
{
  /* START_CBz */
  checkCP2usable();
  if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if (((readCapReg(cb)) == null_cap) ^ invert) then
    {
      let offset : bits(64) = (EXTS(imm @ 0b00) + 4) in
      delayedPC     = PC + offset;
      branchPending = 0b1;
    }
  /* END_CBz */
}

union clause ast = CJALR : (regno, regno, bool)
function clause execute(CJALR(cd, cb, link)) = 
{
  /* START_CJALR */
  checkCP2usable();
  cb_val = readCapReg(cb);
  cb_ptr = getCapCursor(cb_val);
  cb_top = getCapTop(cb_val);
  cb_base= getCapBase(cb_val);
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
  else if ((cb_ptr % 4) != 0) then
    SignalException(AdEL)
  else
    {
      if (link) then
        let pcc = capRegToCapStruct(PCC) in
        let (success, linkCap) = setCapOffset(pcc, PC+8) in
        if (success) then
            writeCapReg(cd, linkCap)
        else
            assert(false, "");
      delayedPC =  to_bits(64, getCapOffset(cb_val));
      delayedPCC = capStructToCapReg(cb_val);
      branchPending = 0b1;
    }
  /* END_CJALR */
}

union clause ast = CLoad : (regno, regno, regno, bits(8), bool, WordType, bool)
function clause execute (CLoad(rd, cb, rt, offset, signext, width, linked)) =
{
  /* START_CLoad */
  checkCP2usable();
  cb_val = readCapReg(cb);
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
      size   = wordWidthBytes(width);
      cursor = getCapCursor(cb_val);
      vAddr  = cursor + unsigned(rGPR(rt)) + (size*signed(offset));
      vAddr64= to_bits(64, vAddr);
      if ((vAddr + size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if not (isAddressAligned(vAddr64, width)) then
        SignalExceptionBadAddr(AdEL, vAddr64)
      else
        {
          pAddr      = (TLBTranslate(vAddr64, LoadData));
          widthBytes = wordWidthBytes(width);
          memResult : bits(64) = if (linked) then
              {
                CP0LLBit  = 0b1;
                CP0LLAddr = pAddr;
                if widthBytes == 1 then extendLoad(MEMr_reserve_wrapper(pAddr, 1), signext)
                else if widthBytes == 2 then extendLoad(MEMr_reserve_wrapper(pAddr, 2), signext)
                else if widthBytes == 4 then extendLoad(MEMr_reserve_wrapper(pAddr, 4), signext)
                else extendLoad(MEMr_reserve_wrapper(pAddr, 8), signext)
              }
            else
              {
                if widthBytes == 1 then extendLoad(MEMr_wrapper(pAddr, 1), signext)
                else if widthBytes == 2 then extendLoad(MEMr_wrapper(pAddr, 2), signext)
                else if widthBytes == 4 then extendLoad(MEMr_wrapper(pAddr, 4), signext)
                else extendLoad(MEMr_wrapper(pAddr, 8), signext)
              };
          wGPR(rd) = memResult;
        }
    }
  /* END_CLoad */
}

union clause ast = CStore : (regno, regno, regno, regno, bits(8), WordType, bool)

function clause execute (CStore(rs, cb, rt, rd, offset, width, conditional)) =
{
  /* START_CStore */
  checkCP2usable();
  cb_val = readCapReg(cb);
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
      size   = wordWidthBytes(width);
      cursor = getCapCursor(cb_val);
      vAddr  = cursor + unsigned(rGPR(rt)) + (size * signed(offset));
      vAddr64= to_bits(64, vAddr);
      if ((vAddr + size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if not (isAddressAligned(vAddr64, width)) then
        SignalExceptionBadAddr(AdES, vAddr64)
      else
        {
          pAddr  = (TLBTranslate(vAddr64, StoreData));
          rs_val = rGPR(rs);
          if (conditional) then
            {
              success : bool = if (CP0LLBit[0]) then
                  match width
                    {
                      B  => MEMw_conditional_wrapper(pAddr, 1, rs_val[7..0]),
                      H  => MEMw_conditional_wrapper(pAddr, 2, rs_val[15..0]),
                      W  => MEMw_conditional_wrapper(pAddr, 4, rs_val[31..0]),
                      D  => MEMw_conditional_wrapper(pAddr, 8, rs_val)
                    }
                else
                  false;
              wGPR(rd) = EXTZ(success);
            }
            else
          match width
            {
              B  => MEMw_wrapper(pAddr, 1) = rs_val[7..0],
              H  => MEMw_wrapper(pAddr, 2) = rs_val[15..0],
              W  => MEMw_wrapper(pAddr, 4) = rs_val[31..0],
              D  => MEMw_wrapper(pAddr, 8) = rs_val
            }
        }
    }
  /* END_CStore */
}

union clause ast = CSC : (regno, regno, regno, regno, bits(11), bool)
function clause execute (CSC(cs, cb, rt, rd, offset, conditional)) =
{
  /* START_CSC */
  checkCP2usable();
  cs_val = readCapReg(cs);
  cb_val = readCapReg(cb);
  if (register_inaccessible(cs)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cs)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_store) then
    raise_c2_exception(CapEx_PermitStoreViolation, cb)
  else if not (cb_val.permit_store_cap) then
    raise_c2_exception(CapEx_PermitStoreCapViolation, cb)
  else if not (cb_val.permit_store_local_cap) & (cs_val.tag) & not (cs_val.global) then
    raise_c2_exception(CapEx_PermitStoreLocalCapViolation, cb)
  else
    {
      cursor = getCapCursor(cb_val);
      vAddr  = cursor + unsigned(rGPR(rt)) + (16 * signed(offset));
      vAddr64= to_bits(64, vAddr);
      if ((vAddr + cap_size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if ((vAddr % cap_size) != 0) then
        SignalExceptionBadAddr(AdES, vAddr64)
      else
        {
          let (pAddr, noStoreCap) = TLBTranslateC(vAddr64, StoreData) in
          if (cs_val.tag & noStoreCap) then
            raise_c2_exception(CapEx_TLBNoStoreCap, cs)
          else if (conditional) then
            {
              success = if (CP0LLBit[0]) then
                  MEMw_tagged_conditional(pAddr, cs_val.tag, capStructToMemBits(cs_val))
                else
                  false;
              wGPR(rd) = EXTZ(success);
            }
          else
            MEMw_tagged(pAddr, cs_val.tag, capStructToMemBits(cs_val));
        }
    }
  /* END_CSC */
}

union clause ast = CLC : (regno, regno, regno, bits(11), bool)
function clause execute (CLC(cd, cb, rt, offset, linked)) =  
{
  /* START_CLC */
  checkCP2usable();
  cb_val = readCapReg(cb);
  if (register_inaccessible(cd)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cd)
  else if (register_inaccessible(cb)) then
    raise_c2_exception(CapEx_AccessSystemRegsViolation, cb)
  else if not (cb_val.tag) then
    raise_c2_exception(CapEx_TagViolation, cb)
  else if (cb_val.sealed) then
    raise_c2_exception(CapEx_SealViolation, cb)
  else if not (cb_val.permit_load) then
    raise_c2_exception(CapEx_PermitLoadViolation, cb)
  else
    {
      cursor = getCapCursor(cb_val);
      vAddr  = cursor + unsigned(rGPR(rt)) + (16 * signed(offset));
      vAddr64= to_bits(64, vAddr);
      if ((vAddr + cap_size) > getCapTop(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if (vAddr < getCapBase(cb_val)) then
        raise_c2_exception(CapEx_LengthViolation, cb)
      else if ((vAddr % cap_size) != 0) then
        SignalExceptionBadAddr(AdEL, vAddr64)
      else
        {
          let (pAddr, suppressTag) = TLBTranslateC(vAddr64, LoadData) in
          let 'cd = unsigned(cd) in
          if (linked) then
            {
              CP0LLBit  = 0b1;
              CP0LLAddr = pAddr;
              let (tag, mem) = MEMr_tagged_reserve(pAddr) in
              (*CapRegs[cd]) = memBitsToCapBits(tag & (cb_val.permit_load_cap) & (not (suppressTag)), mem);
            }
          else
            {
              let (tag, mem) = MEMr_tagged(pAddr) in
              (*CapRegs[cd]) = memBitsToCapBits(tag & (cb_val.permit_load_cap) & (not (suppressTag)), mem);
            }
        }
    }
  /* END_CLC */
}

union clause ast = C2Dump : regno
function clause execute (C2Dump (rt)) =
    () /* Currently a NOP */
