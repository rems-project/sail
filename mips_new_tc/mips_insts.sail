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

/* misp_insts.sail: mips instruction decode and execute clauses and AST node
   declarations */

/**************************************************************************************/
/* [D]ADD[I][U] various forms of ADD                                                  */
/**************************************************************************************/

/* DADDIU Doubleword Add Immediate Unsigned --
   the simplest possible instruction, no undefined behaviour or exceptions
   reg, reg, immediate */

union clause ast = DADDIU : (regno, regno, imm16)

function clause decode (0b011001 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(DADDIU(rs, rt, imm))

function clause execute (DADDIU (rs, rt, imm)) =
  {
    wGPR(rt) = rGPR(rs) + EXTS(imm)
  }

/* DADDU Doubleword Add Unsigned -- another very simple instruction,
   reg, reg, reg */

union clause ast = DADDU : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101101) =
  Some(DADDU(rs, rt, rd))

function clause execute (DADDU (rs, rt, rd)) =
  {
    wGPR(rd) = rGPR(rs) + rGPR(rt)
  }

/* DADDI Doubleword Add Immediate
   reg, reg, imm with possible exception */

union clause ast = DADDI : (regno, regno, bits(16))

function clause decode (0b011000 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(DADDI(rs, rt, imm))

function clause execute (DADDI (rs, rt, imm)) =
  {
    let sum65 : bits(65) = EXTS(rGPR(rs)) + EXTS(imm) in
    {
      if (sum65[64] != sum65[63]) then
        (SignalException(Ov))
      else
        wGPR(rt) = sum65[63..0]
    }
  }

/* DADD Doubleword Add
   reg, reg, reg with possible exception */

union clause ast = DADD : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101100) =
  Some(DADD(rs, rt, rd))

function clause execute (DADD (rs, rt, rd)) =
  {
    let sum65 : bits(65) = EXTS(rGPR(rs)) + EXTS(rGPR(rt)) in
    {
      if sum65[64] != sum65[63] then
        (SignalException(Ov))
      else
        wGPR(rd) = sum65[63..0]
    }
  }

/* ADD   32-bit add           -- reg, reg, reg with possible undefined behaviour or exception */

union clause ast = ADD : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100000) =
  Some(ADD(rs, rt, rd))

function clause execute (ADD(rs, rt, rd)) =
  {
    opA : bits(64) = rGPR(rs);
    opB : bits(64) = rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) = undefined /* XXX could exit instead */
    else
      let sum33 : bits(33) = EXTS(opA[31 .. 0]) + EXTS(opB[31 .. 0])in
        if sum33[32] != sum33[31] then
          (SignalException(Ov))
        else
	  wGPR(rd) = EXTS(sum33[31..0])
  }

/* ADDI  32-bit add immediate -- reg, reg, imm with possible undefined behaviour or exception */

union clause ast = ADDI : (regno, regno, bits(16))

function clause decode (0b001000 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(ADDI(rs, rt, imm))

function clause execute (ADDI(rs, rt, imm)) =
  {
    opA = rGPR(rs);
    if NotWordVal(opA) then
      wGPR(rt) = undefined /* XXX could exit instead */
    else
      let sum33 : bits(33) = EXTS(opA[31 .. 0]) + EXTS(imm) in
        if sum33[32] != sum33[31] then
          (SignalException(Ov))
        else
	  wGPR(rt) = EXTS(sum33[31..0])
  }

/* ADDU  32-bit add immediate -- reg, reg, reg with possible undefined behaviour */

union clause ast = ADDU : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100001) =
  Some(ADDU(rs, rt, rd))

function clause execute (ADDU(rs, rt, rd)) =
  {
    opA = rGPR(rs);
    opB = rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) = undefined
    else
      wGPR(rd) = EXTS(opA[31..0] + opB[31..0])
  }


/* ADDIU 32-bit add immediate -- reg, reg, imm with possible undefined behaviour */

union clause ast = ADDIU : (regno, regno, bits(16))

function clause decode (0b001001 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(ADDIU(rs, rt, imm))

function clause execute (ADDIU(rs, rt, imm)) =
  {
    opA = rGPR(rs);
    if NotWordVal(opA) then
      wGPR(rt) = undefined /* XXX could exit instead */
    else
      wGPR(rt) = EXTS((opA[31 .. 0]) + EXTS(imm))
  }

/**************************************************************************************/
/* [D]SUB[U] various forms of SUB                                                     */
/**************************************************************************************/

/* DSUBU doubleword subtract 'unsigned' reg, reg, reg */

union clause ast = DSUBU : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101111) =
  Some(DSUBU(rs, rt, rd))

function clause execute (DSUBU (rs, rt, rd)) =
  {
    wGPR(rd) = rGPR(rs) - rGPR(rt)
  }

/* DSUB reg, reg, reg with possible exception */

union clause ast = DSUB : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101110) =
  Some(DSUB(rs, rt, rd))

function clause execute (DSUB (rs, rt, rd)) =
  {
    let temp65 : bits(65) = EXTS(rGPR(rs)) - EXTS(rGPR(rt)) in
    {
      if temp65[64] != temp65[63] then
        (SignalException(Ov))
      else
        wGPR(rd) = temp65[63..0]
    }
  }

/* SUB   32-bit sub           -- reg, reg, reg with possible undefined behaviour or exception */

union clause ast = SUB : (regno, regno, regno)

function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100010) =
  Some(SUB(rs, rt, rd))

function clause execute (SUB(rs, rt, rd)) =
  {
    opA = rGPR(rs);
    opB = rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) = undefined /* XXX could instead */
    else
      let temp33 : bits(33) = EXTS(opA[31..0]) - EXTS(opB[31..0]) in
      if temp33[32] != temp33[31] then
        (SignalException(Ov))
      else
        wGPR(rd) = EXTS(temp33[31..0])
  }

/* SUBU  32-bit 'unsigned' sub -- reg, reg, reg with possible undefined behaviour */

union clause ast = SUBU : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100011) =
    Some(SUBU(rs, rt, rd))

function clause execute (SUBU(rs, rt, rd)) =
  {
    opA = rGPR(rs);
    opB = rGPR(rt);
    if NotWordVal(opA) | NotWordVal(opB) then
      wGPR(rd) = undefined
    else
      wGPR(rd) = EXTS(opA[31..0] - opB[31..0])
  }

/**************************************************************************************/
/* Logical bitwise operations                                                         */
/**************************************************************************************/

/* AND reg, reg, reg */

union clause ast = AND : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100100) =
    Some(AND(rs, rt, rd))

function clause execute (AND (rs, rt, rd)) =
  {
    wGPR(rd) = (rGPR(rs) & rGPR(rt))
  }

/* ANDI reg, reg, imm */

union clause ast = ANDI : (regno, regno, bits(16))
function clause decode (0b001100 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(ANDI(rs, rt, imm))
function clause execute (ANDI (rs, rt, imm)) =
  {
    wGPR(rt) = (rGPR(rs) & EXTZ(imm))
  }

/* OR reg, reg, reg */

union clause ast = OR : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100101) =
  Some(OR(rs, rt, rd))
function clause execute (OR (rs, rt, rd)) =
  {
    wGPR(rd) = (rGPR(rs) | rGPR(rt))
  }

/* ORI reg, reg, imm */

union clause ast = ORI : (regno, regno, bits(16))
function clause decode (0b001101 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(ORI(rs, rt, imm))
function clause execute (ORI (rs, rt, imm)) =
  {
    wGPR(rt) = (rGPR(rs) | EXTZ(imm))
  }

/* NOR reg, reg, reg */

union clause ast = NOR : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100111) =
  Some(NOR(rs, rt, rd))
function clause execute (NOR (rs, rt, rd)) =
  {
    wGPR(rd) = ~(rGPR(rs) | rGPR(rt))
  }

/* XOR reg, reg, reg */

union clause ast = XOR : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b100110) =
  Some(XOR(rs, rt, rd))
function clause execute (XOR (rs, rt, rd)) =
  {
    wGPR(rd) = (rGPR(rs) ^ rGPR(rt))
  }

/* XORI reg, reg, imm */
union clause ast = XORI : (regno, regno, bits(16))
function clause decode (0b001110 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(XORI(rs, rt, imm))
function clause execute (XORI (rs, rt, imm)) =
  {
    wGPR(rt) = (rGPR(rs) ^ EXTZ(imm))
  }

/* LUI reg, imm 32-bit load immediate into upper 16 bits */
union clause ast = LUI : (regno, imm16)
function clause decode (0b001111 @ 0b00000 @ rt : regno @ imm : imm16) =
  Some(LUI(rt, imm))
function clause execute (LUI (rt, imm)) =
  {
    wGPR(rt) = EXTS(imm @ 0x0000)
  }

/**************************************************************************************/
/* 64-bit  shift operations                                                           */
/**************************************************************************************/

/* DSLL reg, reg, imm5 */

union clause ast = DSLL : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111000) =
  Some(DSLL(rt, rd, sa))
function clause execute (DSLL (rt, rd, sa)) =
  {

    wGPR(rd) = (rGPR(rt) << sa)
  }

/* DSLL32 reg, reg, imm5 */

union clause ast = DSLL32 : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111100) =
  Some(DSLL32(rt, rd, sa))
function clause execute (DSLL32 (rt, rd, sa)) =
  {
    wGPR(rd) = (rGPR(rt) << (0b1 @ sa))
  }

/* DSLLV reg, reg, reg */

union clause ast = DSLLV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b010100) =
  Some(DSLLV(rs, rt, rd))
function clause execute (DSLLV (rs, rt, rd)) =
  {
    wGPR(rd) = (rGPR(rt) << ((rGPR(rs))[5 .. 0]))
  }

/* DSRA arithmetic shift duplicating sign bit - reg, reg, imm5 */

union clause ast = DSRA : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111011) =
  Some(DSRA(rt, rd, sa))
function clause execute (DSRA (rt, rd, sa)) =
  {
    temp     = rGPR(rt);
    wGPR(rd) = temp >>_s sa
  }

/* DSRA32 reg, reg, imm5 */

union clause ast = DSRA32 : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111111) =
  Some(DSRA32(rt, rd, sa))
function clause execute (DSRA32 (rt, rd, sa)) =
  {
    temp     = rGPR(rt);
    sa32 = 0b1 @ sa; /* sa+32 */
    wGPR(rd) = temp >>_s sa32
  }

/* DSRAV reg, reg, reg */
union clause ast = DSRAV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b010111) =
  Some(DSRAV(rs, rt, rd))
function clause execute (DSRAV (rs, rt, rd)) =
  {
    temp     = rGPR(rt);
    sa = rGPR(rs)[5..0];
    wGPR(rd) = temp >>_s sa
  }

/* DSRL shift right logical - reg, reg, imm5 */

union clause ast = DSRL : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111010) =
  Some(DSRL(rt, rd, sa))
function clause execute (DSRL (rt, rd, sa)) =
  {
    temp     = rGPR(rt);
    wGPR(rd) = temp >> sa;
  }

/* DSRL32 reg, reg, imm5 */

union clause ast = DSRL32 : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : bits(5) @ 0b111110) =
  Some(DSRL32(rt, rd, sa))
function clause execute (DSRL32 (rt, rd, sa)) =
  {
    temp     = rGPR(rt);
    sa32 = 0b1 @ sa; /* sa+32 */
    wGPR(rd) = temp >> sa32;
  }

/* DSRLV reg, reg, reg */

union clause ast = DSRLV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b010110) =
  Some(DSRLV(rs, rt, rd))
function clause execute (DSRLV (rs, rt, rd)) =
  {
    temp = rGPR(rt);
    sa = rGPR(rs)[5..0];
    wGPR(rd) = temp >> sa;
  }

/**************************************************************************************/
/* 32-bit  shift operations                                                           */
/**************************************************************************************/

/* SLL 32-bit shift left */

union clause ast = SLL : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : regno @ 0b000000) =
  Some(SLL(rt, rd, sa))
function clause execute (SLL(rt, rd, sa)) =
  {
    rt32     = rGPR(rt)[31..0];
    wGPR(rd) = EXTS(rt32 << sa);
  }

/* SLLV 32-bit shift left variable */

union clause ast = SLLV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b000100) =
  Some(SLLV(rs, rt, rd))
function clause execute (SLLV(rs, rt, rd)) =
  {
    sa       = rGPR(rs)[4..0];
    rt32     = rGPR(rt)[31..0];
    wGPR(rd) = EXTS(rt32 << sa)
  }

/* SRA 32-bit arithmetic shift right */

union clause ast = SRA : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : regno @ 0b000011) =
  Some(SRA(rt, rd, sa))
function clause execute (SRA(rt, rd, sa)) =
  {
    temp = rGPR(rt);
    if (NotWordVal(temp)) then
      wGPR(rd) = undefined
    else {
      rt32 = temp[31..0];
      wGPR(rd) = EXTS(rt32 >>_s sa);
    }
  }

/* SRAV 32-bit arithmetic shift right variable */

union clause ast = SRAV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b000111) =
  Some(SRAV(rs, rt, rd))
function clause execute (SRAV(rs, rt, rd)) =
  {
    temp = rGPR(rt);
    sa   = rGPR(rs)[4..0];
    if (NotWordVal(temp)) then
      wGPR(rd) = undefined
    else {
      rt32 = temp[31..0];
      wGPR(rd) = EXTS(rt32 >>_s sa)
    }
  }

/* SRL 32-bit shift right */

union clause ast = SRL : (regno, regno, regno)
function clause decode (0b000000 @ 0b00000 @ rt : regno @ rd : regno @ sa : regno @ 0b000010) =
  Some(SRL(rt, rd, sa))
function clause execute (SRL(rt, rd, sa)) =
  {
    temp = rGPR(rt);
    if (NotWordVal(temp)) then
      wGPR(rd) = undefined
    else {
      rt32 = temp[31..0];
      wGPR(rd) = EXTS(rt32 >> sa);
    }
  }

/* SRLV 32-bit shift right variable */

union clause ast = SRLV : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b000110) =
  Some(SRLV(rs, rt, rd))
function clause execute (SRLV(rs, rt, rd)) =
  {
    temp = rGPR(rt);
    sa   = (rGPR(rs))[4..0];
    if (NotWordVal(temp)) then
      wGPR(rd) = undefined
    else {
      rt32 = temp[31..0];
      wGPR(rd) = EXTS(rt32 >> sa);
    }
  }

/**************************************************************************************/
/* set less than / conditional move                                                    */
/**************************************************************************************/

/* SLT set if less than (signed) */

union clause ast = SLT : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101010) =
  Some(SLT(rs, rt, rd))
function clause execute (SLT(rs, rt, rd)) =
  {
    wGPR(rd) = EXTZ(if (rGPR(rs) <_s rGPR(rt)) then 0b1 else 0b0)
  }

/* SLT set if less than immediate (signed) */

union clause ast = SLTI : (regno, regno, bits(16))
function clause decode (0b001010 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(SLTI(rs, rt, imm))
function clause execute (SLTI(rs, rt, imm)) =
  {
    let imm_val = signed(imm) in
    let rs_val = signed(rGPR(rs)) in
    wGPR(rt) = EXTZ(if (rs_val < imm_val) then 0b1 else 0b0)
  }

/* SLTU set if less than unsigned */

union clause ast = SLTU : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b101011) =
  Some(SLTU(rs, rt, rd))
function clause execute (SLTU(rs, rt, rd)) =
  {
    let rs_val = rGPR(rs) in
    let rt_val = rGPR(rt) in
    wGPR(rd) = EXTZ(if (rs_val <_u rt_val) then 0b1 else 0b0)
  }

/* SLTIU set if less than immediate unsigned */

union clause ast = SLTIU : (regno, regno, bits(16))
function clause decode (0b001011 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(SLTIU(rs, rt, imm))
function clause execute (SLTIU(rs, rt, imm)) =
  {
    let rs_val = rGPR(rs) in
    let immext : bits(64) = EXTS(imm) in /* NB defined to sign extend here even though comparison is unsigned! */
    wGPR(rt) = EXTZ(if (rs_val <_u immext) then 0b1 else 0b0)
  }

/* MOVN move if non-zero */

union clause ast = MOVN : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b001011) =
  Some(MOVN(rs, rt, rd))
function clause execute (MOVN(rs, rt, rd)) =
  {
    if (rGPR(rt) != 0x0000000000000000) then
      wGPR(rd) = rGPR(rs)
  }

/* MOVZ move if zero */

union clause ast = MOVZ : (regno, regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b001010) =
  Some(MOVZ(rs, rt, rd))
function clause execute (MOVZ(rs, rt, rd)) =
  {
    if (rGPR(rt) == 0x0000000000000000) then
      wGPR(rd) = rGPR(rs)
  }

/******************************************************************************/
/* MUL/DIV instructions                                                       */
/******************************************************************************/

/* MFHI move from HI register */
union clause ast = MFHI : regno
function clause decode (0b000000 @ 0b0000000000 @ rd : regno @ 0b00000 @ 0b010000) =
  Some(MFHI(rd))
function clause execute (MFHI(rd)) =
  {
    wGPR(rd) = HI
  }

/* MFLO move from LO register */
union clause ast = MFLO : regno
function clause decode (0b000000 @ 0b0000000000 @ rd : regno @ 0b00000 @ 0b010010) =
  Some(MFLO(rd))
function clause execute (MFLO(rd)) =
  {
    wGPR(rd) = LO
  }

/* MTHI move to HI register */
union clause ast = MTHI : regno
function clause decode (0b000000 @ rs : regno @ 0b000000000000000 @ 0b010001) =
  Some(MTHI(rs))
function clause execute (MTHI(rs)) =
  {
    HI = rGPR(rs)
  }

/* MTLO move to LO register */
union clause ast = MTLO : regno
function clause decode (0b000000 @ rs : regno @ 0b000000000000000 @ 0b010011) =
  Some(MTLO(rs))
function clause execute (MTLO(rs)) =
  {
    LO = rGPR(rs)
  }

/* MUL 32-bit multiply into GPR */
union clause ast = MUL : (regno, regno, regno)
function clause decode (0b011100 @ rs : regno @ rt : regno @ rd : regno @ 0b00000 @ 0b000010) =
  Some(MUL(rs, rt, rd))
function clause execute (MUL(rs, rt, rd)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    result : bits(64) = EXTS((rsVal[31..0]) *_s (rtVal[31..0]));
    wGPR(rd) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
        EXTS(result[31..0]);
    /* HI and LO are technically undefined after MUL, but this causes problems with tests and
       (potentially) context switch so just leave them alone
    HI = undefined;
    LO = undefined;
    */
  }

/* MULT 32-bit multiply into HI/LO */
union clause ast = MULT : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011000) =
  Some(MULT(rs, rt))
function clause execute (MULT(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	(rsVal[31..0]) *_s (rtVal[31..0]);
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* MULTU 32-bit unsignedm rultiply into HI/LO */
union clause ast = MULTU : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011001) =
  Some(MULTU(rs, rt))
function clause execute (MULTU(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	(rsVal[31..0]) *_u (rtVal[31..0]);
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* DMULT 64-bit multiply into HI/LO */
union clause ast = DMULT : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011100) =
  Some(DMULT(rs, rt))
function clause execute (DMULT(rs, rt)) =
  {
    result = rGPR(rs) *_s rGPR(rt);
    HI = (result[127..64]);
    LO = (result[63..0]);
  }

/* DMULTU 64-bit unsigned multiply into HI/LO */
union clause ast = DMULTU : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011101) =
  Some(DMULTU(rs, rt))
function clause execute (DMULTU(rs, rt)) =
  {
    result = rGPR(rs) *_u rGPR(rt);
    HI = (result[127..64]);
    LO = (result[63..0]);
  }

/* MADD 32-bit signed multiply and add into HI/LO */
union clause ast = MADD : (regno, regno)
function clause decode (0b011100 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b000000) =
  Some(MADD(rs, rt))
function clause execute (MADD(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    mul_result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	rsVal[31..0] *_s rtVal[31..0];
    result = mul_result + (HI[31..0] @ LO[31..0]);
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* MADDU 32-bit unsigned multiply and add into HI/LO */
union clause ast = MADDU : (regno, regno)
function clause decode (0b011100 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b000001) =
  Some(MADDU(rs, rt))
function clause execute (MADDU(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    mul_result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	rsVal[31..0] *_u rtVal[31..0];
    result = mul_result + (HI[31..0] @ LO[31..0]);
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* MSUB 32-bit signed multiply and sub from HI/LO */
union clause ast = MSUB : (regno, regno)
function clause decode (0b011100 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b000100) =
  Some(MSUB(rs, rt))
function clause execute (MSUB(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    mul_result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	rsVal[31..0] *_s rtVal[31..0];
    result = (HI[31..0] @ LO[31..0]) - mul_result;
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* MSUBU 32-bit unsigned multiply and sub from HI/LO */
union clause ast = MSUBU : (regno, regno)
function clause decode (0b011100 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b000101) =
  Some(MSUBU(rs, rt))
function clause execute (MSUBU(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    mul_result : bits(64) = if (NotWordVal(rsVal) | NotWordVal(rtVal)) then
        undefined
      else
	rsVal[31..0] *_u rtVal[31..0];
    result = (HI[31..0] @ LO[31..0]) - mul_result;
    HI = EXTS(result[63..32]);
    LO = EXTS(result[31..0]);
  }

/* DIV 32-bit divide into HI/LO */
union clause ast = DIV : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011010) =
  Some(DIV(rs, rt))
function clause execute (DIV(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    let (q, r) =
      if (NotWordVal(rsVal) | NotWordVal(rtVal) | (rtVal == 0x0000000000000000)) then
	(undefined : bits(32), undefined : bits(32))
      else
        let si = signed((rsVal[31..0])) in
        let ti = signed((rtVal[31..0])) in
        let qi = quot_round_zero(si, ti) in
        let ri = si - (ti*qi) in
	(to_bits(32, qi), to_bits(32, ri))
    in
    {
      HI = EXTS(r);
      LO = EXTS(q);
    }
  }

/* DIVU 32-bit unsigned divide into HI/LO */
union clause ast = DIVU : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011011) =
  Some(DIVU(rs, rt))
function clause execute (DIVU(rs, rt)) =
  {
    rsVal = rGPR(rs);
    rtVal = rGPR(rt);
    let (q, r) = 
      if (NotWordVal(rsVal) | NotWordVal(rtVal) | rtVal == 0x0000000000000000) then
	(undefined : bits(32), undefined : bits(32))
      else
        let si = unsigned(rsVal[31..0]) in
        let ti = unsigned(rtVal[31..0]) in
        let qi = quot_round_zero(si, ti) in
        let ri = rem_round_zero(si, ti)   in
	(to_bits(32, qi), to_bits(32, ri))
    in
    {
      HI = EXTS(r);
      LO = EXTS(q);
    }
  }

/* DDIV 64-bit divide into HI/LO */
union clause ast = DDIV : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011110) =
  Some(DDIV(rs, rt))
function clause execute (DDIV(rs, rt)) =
  {
    rsVal = signed(rGPR(rs));
    rtVal = signed(rGPR(rt));
    let (q , r) =
      if (rtVal == 0)
        then (undefined : bits(64), undefined : bits(64))
      else
        let qi = quot_round_zero(rsVal, rtVal) in
        let ri = (rsVal - (qi * rtVal)) in
	(to_bits(64, qi), to_bits(64, ri)) in
    {
      LO    = q;
      HI    = r;
    }
  }

/* DDIV 64-bit divide into HI/LO */
union clause ast = DDIVU : (regno, regno)
function clause decode (0b000000 @ rs : regno @ rt : regno @ 0b00000 @ 0b00000 @ 0b011111) =
  Some(DDIVU(rs, rt))
function clause execute (DDIVU(rs, rt)) =
  {
    rsVal = unsigned(rGPR(rs));
    rtVal = unsigned(rGPR(rt));
    let (q, r) =
      if (rtVal == 0)
        then (undefined  : bits(64), undefined : bits(64))
      else
        let qi = quot_round_zero(rsVal, rtVal) in
        let ri = rem_round_zero(rsVal, rtVal) in
	(to_bits(64, qi), to_bits(64, ri)) in
    {
      LO    = q;
      HI    = r;
    }
  }

/**************************************************************************************/
/* Jump instructions -- unconditional branches                                        */
/**************************************************************************************/

/* J    - jump, the simplest control flow instruction, with branch delay slot */
union clause ast = J : bits(26)
function clause decode (0b000010 @ offset : bits(26)) =
  Some(J(offset))
function clause execute (J(offset)) =
  {
    delayedPC     = (PC + 4)[63..28] @ offset @ 0b00;
    branchPending = 0b1
  }

/* JAL    - jump and link */
union clause ast = JAL : bits(26)
function clause decode (0b000011 @ offset : bits(26)) =
  Some(JAL(offset))
function clause execute (JAL(offset)) =
  {
    delayedPC     = (PC + 4)[63..28] @ offset @ 0b00;
    branchPending = 0b1;
    wGPR(0b11111) = PC + 8;
  }

/* JR -- jump via register */
union clause ast = JR : regno
function clause decode (0b000000 @ rs : regno @ 0b00000 @ 0b00000 @ hint : regno @ 0b001000) =
  Some(JR(rs)) /* hint is ignored */
function clause execute (JR(rs)) =
  {
    delayedPC     = rGPR(rs);
    branchPending = 0b1;
  }

/* JALR -- jump via register with link */
union clause ast = JALR : (regno, regno)
function clause decode (0b000000 @ rs : regno @ 0b00000 @ rd : regno @ hint : regno @ 0b001001) =
  Some(JALR(rs, rd)) /* hint is ignored */
function clause execute (JALR(rs, rd)) =
  {
    delayedPC     = rGPR(rs);
    branchPending = 0b1;
    wGPR(rd)      = PC + 8;
  }

/**************************************************************************************/
/* B[N]EQ[L]  - branch on (not) equal (likely)                                        */
/* Conditional branch instructions with two register operands                         */
/**************************************************************************************/

union clause ast = BEQ : (regno, regno, imm16, bool, bool)
function clause decode (0b000100 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(BEQ(rs, rt, imm, false, false))  /* BEQ  */
function clause decode (0b010100 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(BEQ(rs, rt, imm, false, true))   /* BEQL */
function clause decode (0b000101 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(BEQ(rs, rt, imm, true , false))  /* BNE  */
function clause decode (0b010101 @ rs : regno @ rt : regno @ imm : imm16) =
  Some(BEQ(rs, rt, imm, true , true))   /* BNEL */
function clause execute (BEQ(rs, rd, imm, ne, likely)) =
  {
    if ((rGPR(rs) == rGPR(rd)) ^ ne) then
      {
        let offset : bits(64) = (EXTS(imm @ 0b00) + 4) in
        delayedPC     = PC + offset;
        branchPending = 0b1;
      }
    else
      {
        if (likely) then
          nextPC = PC + 8; /* skip branch delay */
      }
  }

/*

   Branches comparing with zero (single register operand, possible link in r31)
*/

/**************************************************************************************/
/* BGEZ[AL][L] - branch on comparison with zero (possibly  link, likely)              */
/* Conditional branch instructions with single register operand                       */
/**************************************************************************************/

union clause ast = BCMPZ : (regno, imm16, Comparison, bool, bool)
function clause decode (0b000001 @ rs : regno @ 0b00000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LT, false, false)) /* BLTZ */
function clause decode (0b000001 @ rs : regno @ 0b10000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LT, true, false))  /* BLTZAL */
function clause decode (0b000001 @ rs : regno @ 0b00010 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LT, false, true))  /* BLTZL */
function clause decode (0b000001 @ rs : regno @ 0b10010 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LT, true, true))   /* BLTZALL */

function clause decode (0b000001 @ rs : regno @ 0b00001 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GE, false, false)) /* BGEZ */
function clause decode (0b000001 @ rs : regno @ 0b10001 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GE, true, false))  /* BGEZAL */
function clause decode (0b000001 @ rs : regno @ 0b00011 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GE, false, true))  /* BGEZL */
function clause decode (0b000001 @ rs : regno @ 0b10011 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GE, true, true))   /* BGEZALL */

function clause decode (0b000111 @ rs : regno @ 0b00000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GT, false, false)) /* BGTZ */
function clause decode (0b010111 @ rs : regno @ 0b00000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, GT, false, true))  /* BGTZL */

function clause decode (0b000110 @ rs : regno @ 0b00000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LE, false, false)) /* BLEZ */
function clause decode (0b010110 @ rs : regno @ 0b00000 @ imm : imm16) =
  Some(BCMPZ(rs, imm, LE, false, true))  /* BLEZL */

function clause execute (BCMPZ(rs, imm, cmp, link, likely)) =
  {
    linkVal = PC + 8;
    regVal = rGPR(rs);
    condition = compare(cmp, regVal, EXTZ(0b0));
    if (condition) then
      {
        let offset : bits(64) = (EXTS(imm @ 0b00) + 4) in
        delayedPC     =  PC + offset;
        branchPending = 0b1;
      }
    else if (likely) then
      {
        nextPC = PC + 8  /* skip branch delay */
      };
    if (link) then
      wGPR(0b11111) = linkVal
  }

/**************************************************************************************/
/* SYSCALL/BREAK/WAIT/Trap                                                            */
/**************************************************************************************/

/* Co-opt syscall 0xfffff for use as thread start in pccmem  */
union clause ast = SYSCALL_THREAD_START : unit
function clause decode (0b000000 @ 0xfffff @ 0b001100) =
  Some(SYSCALL_THREAD_START)
function clause execute (SYSCALL_THREAD_START) = ()


/* fake stop fetching instruction for ppcmem, execute doesn't do anything,
   decode never produces it */

union clause ast = ImplementationDefinedStopFetching : unit
function clause execute (ImplementationDefinedStopFetching) = ()


union clause ast = SYSCALL : unit
function clause decode (0b000000 @ code : bits(20) @ 0b001100) =
  Some(SYSCALL) /* code is ignored */
function clause execute (SYSCALL) =
  {
    (SignalException(Sys))
  }

/* BREAK is identical to SYSCALL exception for the exception raised */
union clause ast = BREAK : unit
function clause decode (0b000000 @ code : bits(20) @ 0b001101) =
  Some(BREAK) /* code is ignored */
function clause execute (BREAK) =
  {
    (SignalException(Bp))
  }

/* Accept WAIT as a NOP */
union clause ast = WAIT : unit
function clause decode (0b010000 @ 0x80000 @ 0b100000) =
  Some(WAIT) /* we only accept code == 0 */
function clause execute (WAIT) = {
  nextPC = PC;
}

/* Trap instructions with two register operands */
union clause ast = TRAPREG : (regno, regno, Comparison)
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110000) =
  Some(TRAPREG(rs, rt, GE)) /* TGE */
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110001) =
  Some(TRAPREG(rs, rt, GEU)) /* TGEU */
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110010) =
  Some(TRAPREG(rs, rt, LT)) /* TLT */
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110011) =
  Some(TRAPREG(rs, rt, LTU)) /* TLTU */
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110100) =
  Some(TRAPREG(rs, rt, EQ)) /* TEQ */
function clause decode (0b000000 @ rs : regno @ rt : regno @ code : bits(10) @ 0b110110) =
  Some(TRAPREG(rs, rt, NE)) /* TNE */
function clause execute (TRAPREG(rs, rt, cmp)) =
  {
    rs_val = rGPR(rs);
    rt_val = rGPR(rt);
    condition = compare(cmp, rs_val, rt_val);
    if (condition) then
      (SignalException(Tr))
  }


/* Trap instructions with one register and one immediate operand */
union clause ast = TRAPIMM : (regno, imm16, Comparison)
function clause decode (0b000001 @ rs : regno @ 0b01100 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, EQ)) /* TEQI */
function clause decode (0b000001 @ rs : regno @ 0b01110 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, NE)) /* TNEI */
function clause decode (0b000001 @ rs : regno @ 0b01000 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, GE)) /* TGEI */
function clause decode (0b000001 @ rs : regno @ 0b01001 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, GEU)) /* TGEIU */
function clause decode (0b000001 @ rs : regno @ 0b01010 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, LT))  /* TLTI */
function clause decode (0b000001 @ rs : regno @ 0b01011 @ imm : imm16) =
  Some(TRAPIMM(rs, imm, LTU)) /* TLTIU */
function clause execute (TRAPIMM(rs, imm, cmp)) =
  {
    rs_val = rGPR(rs);
    imm_val : bits(64) = EXTS(imm);
    condition = compare(cmp, rs_val, imm_val);
    if (condition) then
      (SignalException(Tr))
  }

/**************************************************************************************/
/* Load instructions -- various width/signs                                           */
/**************************************************************************************/

union clause ast = Load : (WordType, bool, bool, regno, regno, imm16)
function clause decode (0b100000 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(B, true,  false, base, rt, offset)) /* LB */
function clause decode (0b100100 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(B, false, false, base, rt, offset)) /* LBU */
function clause decode (0b100001 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(H, true,  false, base, rt, offset)) /* LH */
function clause decode (0b100101 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(H, false, false, base, rt, offset)) /* LHU */
function clause decode (0b100011 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(W, true,  false, base, rt, offset)) /* LW */
function clause decode (0b100111 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(W, false, false, base, rt, offset)) /* LWU */
function clause decode (0b110111 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(D, false, false, base, rt, offset)) /* LD */
function clause decode (0b110000 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(W, true,  true, base, rt, offset))  /* LL */
function clause decode (0b110100 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Load(D, false, true, base, rt, offset))  /* LLD */

val extendLoad : forall 'sz, 'sz <= 64 .  (bits('sz), bool) -> bits(64) effect pure
function extendLoad(memResult, sign) = {
  if (sign) then
    EXTS(memResult)
  else
    EXTZ(memResult)
}

function clause execute (Load(width, sign, linked, base, rt, offset)) =
  {
    vAddr : bits(64) = addrWrapper(EXTS(offset) + rGPR(base), LoadData, width);
    if ~ (isAddressAligned(vAddr, width)) then
      (SignalExceptionBadAddr(AdEL, vAddr)) /* unaligned access */
    else
      let pAddr = (TLBTranslate(vAddr, LoadData)) in
          {
            memResult : bits(64) = if (linked) then
                {
                  CP0LLBit  = 0b1;
                  CP0LLAddr = pAddr;
                  match width {
                   B => extendLoad(MEMr_reserve_wrapper(pAddr, 1), sign),
                   H => extendLoad(MEMr_reserve_wrapper(pAddr, 2), sign),
                   W => extendLoad(MEMr_reserve_wrapper(pAddr, 4), sign),
                   D => extendLoad(MEMr_reserve_wrapper(pAddr, 8), sign)
                  }
                }
              else
                {
                  match width {
                   B => extendLoad(MEMr_wrapper(pAddr, 1), sign),
                   H => extendLoad(MEMr_wrapper(pAddr, 2), sign),
                   W => extendLoad(MEMr_wrapper(pAddr, 4), sign),
                   D => extendLoad(MEMr_wrapper(pAddr, 8), sign)
                  }
                };
            wGPR(rt) = memResult
          }
  }

/**************************************************************************************/
/* Store instructions -- various widths                                               */
/**************************************************************************************/

union clause ast = Store : (WordType, bool, regno, regno, imm16)
function clause decode (0b101000 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(B, false, base, rt, offset)) /* SB */
function clause decode (0b101001 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(H, false, base, rt, offset)) /* SH */
function clause decode (0b101011 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(W, false, base, rt, offset)) /* SW */
function clause decode (0b111111 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(D, false, base, rt, offset)) /* SD */
function clause decode (0b111000 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(W, true, base, rt, offset))  /* SC */
function clause decode (0b111100 @ base : regno @ rt : regno @ offset : imm16) =
  Some(Store(D, true, base, rt, offset))  /* SCD */
function clause execute (Store(width, conditional, base, rt, offset)) =
      {
        vAddr : bits(64) = addrWrapper(EXTS(offset) + rGPR(base), StoreData, width);
        rt_val = rGPR(rt);
        if ~ (isAddressAligned(vAddr, width)) then
          (SignalExceptionBadAddr(AdES, vAddr)) /* unaligned access */
        else
          let pAddr = (TLBTranslate(vAddr, StoreData)) in
          {
                if (conditional) then
                  {
		    success : bool = if (CP0LLBit[0]) then match width
                    {
                      B  => MEMw_conditional_wrapper(pAddr, 1, rt_val[7..0]),
                      H  => MEMw_conditional_wrapper(pAddr, 2, rt_val[15..0]),
                      W  => MEMw_conditional_wrapper(pAddr, 4, rt_val[31..0]),
                      D  => MEMw_conditional_wrapper(pAddr, 8, rt_val)
                    } else false;
		    wGPR(rt) = EXTZ(success)
                  }
                else
                  match width
                    {
                      B  => MEMw_wrapper(pAddr, 1) = rt_val[7..0],
                      H  => MEMw_wrapper(pAddr, 2) = rt_val[15..0],
                      W  => MEMw_wrapper(pAddr, 4) = rt_val[31..0],
                      D  => MEMw_wrapper(pAddr, 8) = rt_val
                    }
          }
      }

/* LWL   - Load word left (big-endian only) */

union clause ast = LWL : (regno, regno, bits(16))
function clause decode(0b100010 @ base : regno @ rt : regno @ offset : imm16) =
      Some(LWL(base, rt, offset))
function clause execute(LWL(base, rt, offset)) =
      {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), LoadData, W);
        let pAddr = (TLBTranslate(vAddr, LoadData)) in
          {
            mem_val = MEMr_wrapper (pAddr[63..2] @ 0b00, 4); /* read word of interest */
            reg_val = rGPR(rt);
            result : bits(32) = match vAddr[1..0]
              {
                0b00  => mem_val,
                0b01  => mem_val[23..0] @ reg_val[07..0],
                0b10  => mem_val[15..0] @ reg_val[15..0],
                0b11  => mem_val[07..0] @ reg_val[23..0]
	      };
	    wGPR(rt) = EXTS(result);
          }
      }
union clause ast = LWR : (regno, regno, bits(16))
function clause decode(0b100110 @ base : regno @ rt : regno @ offset : imm16) =
      Some(LWR(base, rt, offset))
function clause execute(LWR(base, rt, offset)) =
      {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), LoadData, W);
        let pAddr = (TLBTranslate(vAddr, LoadData)) in
          {
            mem_val = MEMr_wrapper(pAddr[63..2] @ 0b00, 4); /* read word of interest */
            reg_val = rGPR(rt);
            result : bits(32) = match vAddr[1..0]
              {
                0b00  => reg_val[31..8]  @ mem_val[31..24],
                0b01  => reg_val[31..16] @ mem_val[31..16],
                0b10  => reg_val[31..24] @ mem_val[31..8],
                0b11  => mem_val
              };
	    wGPR(rt) = EXTS(result)
          }
      }

/* SWL   - Store word left */
union clause ast = SWL : (regno, regno, bits(16))
function clause decode(0b101010 @ base : regno @ rt : regno @ offset : imm16) =
      Some(SWL(base, rt, offset))
function clause execute(SWL(base, rt, offset)) =
      {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), StoreData, W);
        let pAddr = TLBTranslate(vAddr, StoreData) in
          {
            reg_val = rGPR(rt);
            match vAddr[1..0]
            {
              0b00  => (MEMw_wrapper(pAddr, 4) = reg_val[31..0]),
              0b01  => (MEMw_wrapper(pAddr, 3) = reg_val[31..8]),
              0b10  => (MEMw_wrapper(pAddr, 2) = reg_val[31..16]),
              0b11  => (MEMw_wrapper(pAddr, 1) = reg_val[31..24])
            }
          }
      }

union clause ast = SWR : (regno, regno, bits(16))
function clause decode(0b101110 @ base : regno @ rt : regno @ offset : imm16) =
      Some(SWR(base, rt, offset))
function clause execute(SWR(base, rt, offset)) =
      {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), StoreData, W);
        let pAddr = TLBTranslate(vAddr, StoreData) in
          {
            wordAddr = pAddr[63..2] @ 0b00;
            reg_val = rGPR(rt);
            match vAddr[1..0]
              {
                0b00  => (MEMw_wrapper(wordAddr, 1) = reg_val[7..0]),
                0b01  => (MEMw_wrapper(wordAddr, 2) = reg_val[15..0]),
                0b10  => (MEMw_wrapper(wordAddr, 3) = reg_val[23..0]),
                0b11  => (MEMw_wrapper(wordAddr, 4) = reg_val[31..0])
              }
          }
      }

/* Load double-word left */
union clause ast = LDL : (regno, regno, bits(16))
function clause decode(0b011010 @ base : regno @ rt : regno @ offset : imm16) =
  Some(LDL(base, rt, offset))
function clause execute(LDL(base, rt, offset)) =
  {
    /* XXX length check not quite right, but conservative */
    vAddr = addrWrapper(EXTS(offset) + rGPR(base), LoadData, D);
    let pAddr = TLBTranslate(vAddr, StoreData) in
      {
        mem_val = MEMr_wrapper(pAddr[63..3] @ 0b000, 8); /* read double of interest */
        reg_val = rGPR(rt);
        wGPR(rt) = match vAddr[2..0]
              {
                0b000  => mem_val,
                0b001  => mem_val[55..0] @ reg_val[7..0],
                0b010  => mem_val[47..0] @ reg_val[15..0],
                0b011  => mem_val[39..0] @ reg_val[23..0],
                0b100  => mem_val[31..0] @ reg_val[31..0],
                0b101  => mem_val[23..0] @ reg_val[39..0],
                0b110  => mem_val[15..0] @ reg_val[47..0],
                0b111  => mem_val[07..0] @ reg_val[55..0]
              };
      }
  }

/* Load double-word right */
union clause ast = LDR : (regno, regno, bits(16))
function clause decode(0b011011 @ base : regno @ rt : regno @ offset : imm16) =
  Some(LDR(base, rt, offset))
function clause execute(LDR(base, rt, offset)) =
  {
    /* XXX length check not quite right, but conservative */
    vAddr = addrWrapper(EXTS(offset) + rGPR(base), LoadData, D);
    let pAddr = TLBTranslate(vAddr, StoreData) in
      {
        mem_val = MEMr_wrapper(pAddr[63..3] @ 0b000, 8); /* read double of interest */
        reg_val = rGPR(rt);
        wGPR(rt)  = match vAddr[2..0]
              {
                0b000  => reg_val[63..08] @ mem_val[63..56],
                0b001  => reg_val[63..16] @ mem_val[63..48],
                0b010  => reg_val[63..24] @ mem_val[63..40],
                0b011  => reg_val[63..32] @ mem_val[63..32],
                0b100  => reg_val[63..40] @ mem_val[63..24],
                0b101  => reg_val[63..48] @ mem_val[63..16],
                0b110  => reg_val[63..56] @ mem_val[63..08],
                0b111  => mem_val
              };
      }
  }

/* SDL   - Store double-word left */
union clause ast = SDL : (regno, regno, bits(16))
function clause decode(0b101100 @ base : regno @ rt : regno @ offset : imm16) =
      Some(SDL(base, rt, offset))
function clause execute(SDL(base, rt, offset)) =
      {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), StoreData, D);
        let pAddr = TLBTranslate(vAddr, StoreData) in
          {
            reg_val = rGPR(rt);
            match vAddr[2..0]
            {
              0b000  => (MEMw_wrapper(pAddr, 8) = reg_val[63..00]),
              0b001  => (MEMw_wrapper(pAddr, 7) = reg_val[63..08]),
              0b010  => (MEMw_wrapper(pAddr, 6) = reg_val[63..16]),
              0b011  => (MEMw_wrapper(pAddr, 5) = reg_val[63..24]),
              0b100  => (MEMw_wrapper(pAddr, 4) = reg_val[63..32]),
              0b101  => (MEMw_wrapper(pAddr, 3) = reg_val[63..40]),
              0b110  => (MEMw_wrapper(pAddr, 2) = reg_val[63..48]),
              0b111  => (MEMw_wrapper(pAddr, 1) = reg_val[63..56])
            }
          }
      }


/* SDR   - Store double-word right */
union clause ast = SDR : (regno, regno, bits(16))
function clause decode(0b101101 @ base : regno @ rt : regno @ offset : imm16) =
      Some(SDR(base, rt, offset))
function clause execute(SDR(base, rt, offset)) =
  {
        /* XXX length check not quite right, but conservative */
        vAddr = addrWrapper(EXTS(offset) + rGPR(base), StoreData, D);
        let pAddr = TLBTranslate(vAddr, StoreData) in
          {
            reg_val = rGPR(rt);
            wordAddr = pAddr[63..3] @ 0b000;
            match vAddr[2..0]
            {
              0b000  => (MEMw_wrapper(wordAddr, 1) = reg_val[07..0]),
              0b001  => (MEMw_wrapper(wordAddr, 2) = reg_val[15..0]),
              0b010  => (MEMw_wrapper(wordAddr, 3) = reg_val[23..0]),
              0b011  => (MEMw_wrapper(wordAddr, 4) = reg_val[31..0]),
              0b100  => (MEMw_wrapper(wordAddr, 5) = reg_val[39..0]),
              0b101  => (MEMw_wrapper(wordAddr, 6) = reg_val[47..0]),
              0b110  => (MEMw_wrapper(wordAddr, 7) = reg_val[55..0]),
              0b111  => (MEMw_wrapper(wordAddr, 8) = reg_val[63..0])
            }
          }
      }

/* CACHE - manipulate (non-existent) caches */

union clause ast = CACHE : (regno, regno, bits(16))
function clause decode (0b101111 @ base : regno @ op : regno @ imm : imm16) =
  Some(CACHE(base, op, imm))
function clause execute (CACHE(base, op, imm)) =
  checkCP0Access () /* pretty much a NOP because no caches */

/* PREF - prefetching into (non-existent) caches */

union clause ast = PREF : (regno, regno, bits(16))
function clause decode (0b110011 @ base : regno @ op : regno @ imm : imm16) =
  Some(PREF(base, op, imm))
function clause execute (PREF(base, op, imm)) =
  () /* XXX NOP */


/* SYNC  - Memory barrier */
union clause ast = SYNC : unit
function clause decode (0b000000 @ 0b00000 @ 0b00000 @ 0b00000 @ stype : regno @ 0b001111) =
  Some(SYNC) /* stype is currently ignored */
function clause execute(SYNC) =
  MEM_sync()

union clause ast = MFC0 : (regno, regno, bits(3), bool)
function clause decode (0b010000 @ 0b00000 @ rt : regno @ rd : regno @ 0b00000000 @ sel : bits(3)) =
  Some(MFC0(rt, rd, sel, false)) /* MFC0 */
function clause decode (0b010000 @ 0b00001 @ rt : regno @ rd : regno @ 0b00000000 @ sel : bits(3)) =
  Some(MFC0(rt, rd, sel, true))  /* DMFC0 */
function clause execute (MFC0(rt, rd, sel, double)) = {
  checkCP0Access();
  let result : bits(64) = match (rd, sel)
        {
          (0b00000,0b000) => let idx : bits(31) = EXTZ(TLBIndex) in
			         (0x00000000 @ TLBProbe @ idx),  /* 0, TLB Index */
          (0b00001,0b000) => EXTZ(TLBRandom),    /* 1, TLB Random */
          (0b00010,0b000) => TLBEntryLo0.bits(), /* 2, TLB EntryLo0 */
          (0b00011,0b000) => TLBEntryLo1.bits(), /* 3, TLB EntryLo1 */
          (0b00100,0b000) => TLBContext.bits(),  /* 4, TLB Context */
          (0b00101,0b000) => EXTZ(TLBPageMask @ 0x000), /* 5, TLB PageMask */
          (0b00110,0b000) => EXTZ(TLBWired),   /* 6, TLB Wired */
          (0b00111,0b000) => EXTZ(CP0HWREna),  /* 7, HWREna */
          (0b01000,0b000) => CP0BadVAddr,      /* 8, BadVAddr reg */
          (0b01000,0b001) => EXTZ(0b0),        /* 8, BadInstr reg XXX TODO */
          (0b01001,0b000) => EXTZ(CP0Count),   /* 9, Count reg */
          (0b01010,0b000) => TLBEntryHi.bits(),/* 10, TLB EntryHi */
          (0b01011,0b000) => EXTZ(CP0Compare), /* 11, Compare reg */
          (0b01100,0b000) => EXTZ(CP0Status.bits()),  /* 12, Status reg */
          (0b01101,0b000) => EXTZ(CP0Cause.bits()),   /* 13, Cause reg */
          (0b01110,0b000) => CP0EPC,           /* 14, EPC */
          (0b01111,0b000) => EXTZ(0x00000400), /* 15, sel 0: PrID processor ID */
          (0b01111,0b110) => EXTZ(0b0),        /* 15, sel 6: CHERI core ID */
          (0b01111,0b111) => EXTZ(0b0),        /* 15, sel 7: CHERI thread ID */
          (0b10000,0b000) => EXTZ(0b1 /* M */      /* 16, sel 0: Config0 */
                                 @ 0b000000000000000 /* Impl */
                                 @ 0b1               /* BE */
                                 @ 0b10              /* AT */
                                 @ 0b000             /* AR */
                                 @ 0b001             /* MT standard TLB */
                                 @ 0b0000            /* zero */
                                 @ 0b000),
          (0b10000,0b001) => EXTZ( /* 16, sel 1: Config1 */
                                          0b1      /* M */
                                        @ TLBIndexMax /* MMU size-1 */
                                        @ 0b000    /* IS icache sets */
                                        @ 0b000    /* IL icache lines */
                                        @ 0b000    /* IA icache assoc. */
                                        @ 0b000    /* DS dcache sets */
                                        @ 0b000    /* DL dcache lines */
                                        @ 0b000    /* DA dcache assoc. */
			       	 @ bool_to_bits(have_cp2) /* C2 CP2 presence */
                                        @ 0b0      /* MD MDMX implemented */
                                        @ 0b0      /* PC performance counters */
                                        @ 0b0      /* WR watch registers */
                                        @ 0b0      /* CA 16e code compression */
                                        @ 0b0      /* EP EJTAG */
                                        @ 0b0),     /* FP FPU present */
          (0b10000,0b010) => EXTZ( /* 16, sel 2: Config2 */
                                          0b1     /* M */
                                        @ 0b000   /* TU L3 control  */
                                        @ 0b0000  /* TS L3 sets */
                                        @ 0b0000  /* TL L3 lines */
                                        @ 0b0000  /* TA L3 assoc. */
                                        @ 0b0000  /* SU L2 control */
                                        @ 0b0000  /* SS L2 sets */
                                        @ 0b0000  /* SL L2 lines */
                                        @ 0b0000), /* SA L2 assoc. */
          (0b10000,0b011) => 0x0000000000002000, /* 16, sel 3: Config3 zero except for bit 13 == ulri */
          (0b10000,0b101) => 0x0000000000000000, /* 16, sel 5: Config5 beri specific -- no extended TLB */
          (0b10001,0b000) => CP0LLAddr,        /* 17, sel 0: LLAddr */
          (0b10010,0b000) => EXTZ(0b0),        /* 18, WatchLo */
          (0b10011,0b000) => EXTZ(0b0),        /* 19, WatchHi */
          (0b10100,0b000) => TLBXContext.bits(), /* 20, XContext */
          (0b11110,0b000) => CP0ErrorEPC,      /* 30, ErrorEPC */
          _               => (SignalException(ResI))
        } in
  wGPR(rt) = if (double) then result else EXTS(result[31..0])
}

/* simulator halt instruction "MTC0 rt, r23" (cheri specific behaviour) */
union clause ast = HCF : unit
function clause decode (0b010000 @ 0b00100 @ rt : regno @ 0b10111 @ 0b00000000000) =
  Some(HCF)

function clause decode (0b010000 @ 0b00100 @ rt : regno @ 0b11010 @ 0b00000000000) =
  Some(HCF)

function clause execute (HCF) =
  () /* halt instruction actually executed by interpreter framework */

union clause ast = MTC0 : (regno, regno, bits(3), bool)
function clause decode (0b010000 @ 0b00100 @ rt : regno @ rd : regno @ 0b00000000 @ sel : bits(3)) =
  Some(MTC0(rt, rd, sel, false)) /* MTC0 */
function clause decode (0b010000 @ 0b00101 @ rt : regno @ rd : regno @ 0b00000000 @ sel : bits(3)) =
  Some(MTC0(rt, rd, sel, true))  /* DMTC0 */
function clause execute (MTC0(rt, rd, sel, double)) = {
  checkCP0Access();
  let reg_val = rGPR(rt) in
  match (rd, sel)
    {
      (0b00000,0b000) => TLBIndex = mask(reg_val), /* NB no write to TLBProbe */
      (0b00001,0b000) => (),                       /* TLBRandom is read only */
      (0b00010,0b000) => TLBEntryLo0->bits() = reg_val,
      (0b00011,0b000) => TLBEntryLo1->bits() = reg_val,
      (0b00100,0b000) => TLBContext->PTEBase() = reg_val[63..23],
      (0b00100,0b010) => CP0UserLocal = reg_val,
      (0b00101,0b000) => TLBPageMask  = reg_val[28..13],
      (0b00110,0b000) => {
        TLBWired     = mask(reg_val);
        TLBRandom    = TLBIndexMax;
      },
      (0b00111,0b000) => CP0HWREna = (reg_val[31..29] @ 0b0000000000000000000000000 @ reg_val[3..0]),
      (0b01000,0b000) => (), /* BadVAddr read only */
      (0b01001,0b000) => CP0Count = reg_val[31..0],
      (0b01010,0b000) => {
        TLBEntryHi->R()    = reg_val[63..62];
        TLBEntryHi->VPN2() = reg_val[39..13];
        TLBEntryHi->ASID() = reg_val[7..0];
      },
      (0b01011,0b000) => {  /* 11, sel 0: Compare reg */
	CP0Compare = reg_val[31..0];
        CP0Cause->IP() = CP0Cause.IP() & 0x7f; /* clear IP7 */
      },
      (0b01100,0b000) => {  /* 12 Status */
        CP0Status->CU()  = reg_val[31..28];
        CP0Status->BEV() = reg_val[22];
        CP0Status->IM()  = reg_val[15..8];
        CP0Status->KX()  = reg_val[7];
        CP0Status->SX()  = reg_val[6];
        CP0Status->UX()  = reg_val[5];
        CP0Status->KSU() = reg_val[4..3];
        CP0Status->ERL() = reg_val[2];
        CP0Status->EXL() = reg_val[1];
        CP0Status->IE()  = reg_val[0];
      },
      (0b01101,0b000) => {   /* 13 Cause */
        CP0Cause->IV() = reg_val[23]; /* TODO special interrupt vector not implemeneted */
        let ip = CP0Cause.IP() in
        CP0Cause->IP() = ((ip[7..2]) @ (reg_val[9..8]));
      },
      (0b01110,0b000) => CP0EPC = reg_val, /* 14, EPC */
      (0b10000,0b000) => (), /* XXX ignore K0 cache config  16: Config0 */
      (0b10100,0b000) => TLBXContext->XPTEBase() = reg_val[63..33],
      (0b11110,0b000) => CP0ErrorEPC = reg_val, /* 30, ErrorEPC */
      _               => (SignalException(ResI))
    }
}

val TLBWriteEntry : TLBIndexT -> unit effect {rreg, wreg, escape}
function TLBWriteEntry(idx) = {
  pagemask = TLBPageMask;
  match pagemask {
      0x0000  => (),
      0x0003  => (),
      0x000f  => (),
      0x003f  => (),
      0x00ff  => (),
      0x03ff  => (),
      0x0fff  => (),
      0x3fff  => (),
      0xffff  => (),
      _       => (SignalException(MCheck))
  };
  let i as atom(_) = unsigned(idx) in
  let entry = TLBEntries[i] in {
    entry.pagemask() = pagemask;
    entry.r()        = TLBEntryHi.R();
    entry.vpn2()     = TLBEntryHi.VPN2();
    entry.asid()     = TLBEntryHi.ASID();
    entry.g()        = ((TLBEntryLo0.G()) & (TLBEntryLo1.G()));
    entry.valid()    = bitone;
    entry.caps0()    = TLBEntryLo0.CapS();
    entry.capl0()    = TLBEntryLo0.CapL();
    entry.pfn0()     = TLBEntryLo0.PFN();
    entry.c0()       = TLBEntryLo0.C();
    entry.d0()       = TLBEntryLo0.D();
    entry.v0()       = TLBEntryLo0.V();
    entry.caps1()    = TLBEntryLo1.CapS();
    entry.capl1()    = TLBEntryLo1.CapL();
    entry.pfn1()     = TLBEntryLo1.PFN();
    entry.c1()       = TLBEntryLo1.C();
    entry.d1()       = TLBEntryLo1.D();
    entry.v1()       = TLBEntryLo1.V();
  }
}

union clause ast = TLBWI : unit
function clause decode (0b010000 @ 0b10000000000000000000 @ 0b000010) = Some(TLBWI : ast)
function clause execute (TLBWI) = {
  checkCP0Access();
  TLBWriteEntry(TLBIndex);
}

union clause ast = TLBWR : unit
function clause decode (0b010000 @ 0b10000000000000000000 @ 0b000110) = Some(TLBWR : ast)
function clause execute (TLBWR) = {
  checkCP0Access();
  TLBWriteEntry(TLBRandom);
}

union clause ast = TLBR : unit
function clause decode (0b010000 @ 0b10000000000000000000 @ 0b000001) = Some(TLBR : ast)
function clause execute (TLBR) = {
  checkCP0Access();
  let i as atom(_) = unsigned(TLBIndex) in
  let entry = reg_deref(TLBEntries[i]) in {
    TLBPageMask        = entry.pagemask();
    TLBEntryHi->R()    = entry.r();
    TLBEntryHi->VPN2() = entry.vpn2();
    TLBEntryHi->ASID() = entry.asid();
    TLBEntryLo0->CapS()= entry.caps0();
    TLBEntryLo0->CapL()= entry.capl0();
    TLBEntryLo0->PFN() = entry.pfn0();
    TLBEntryLo0->C()   = entry.c0();
    TLBEntryLo0->D()   = entry.d0();
    TLBEntryLo0->V()   = entry.v0();
    TLBEntryLo0->G()   = entry.g();
    TLBEntryLo1->CapS()= entry.caps1();
    TLBEntryLo1->CapL()= entry.capl1();
    TLBEntryLo1->PFN() = entry.pfn1();
    TLBEntryLo1->C()   = entry.c1();
    TLBEntryLo1->D()   = entry.d1();
    TLBEntryLo1->V()   = entry.v1();
    TLBEntryLo1->G()   = entry.g();
  }
}

union clause ast = TLBP : unit
function clause decode (0b010000 @ 0b10000000000000000000 @ 0b001000) = Some(TLBP : ast)
function clause execute ((TLBP)) = {
  checkCP0Access();
  let result = tlbSearch(TLBEntryHi.bits()) in
  match result {
    (Some(idx))  => {
      TLBProbe = [bitzero];
      TLBIndex = idx;
    },
    None  => {
      TLBProbe = [bitone];
      TLBIndex = 0b000000;
    }
  }
}

union clause ast = RDHWR : (regno, regno)
function clause decode (0b011111 @ 0b00000 @ rt : regno @ rd : regno @ 0b00000 @ 0b111011) =
  Some(RDHWR(rt, rd))
function clause execute (RDHWR(rt, rd)) = {
  let accessLevel = getAccessLevel() in
  let haveAccessLevel : bool = accessLevel == Kernel in
  let haveCU0 : bool = bitone == (CP0Status.CU()[0]) in
  let rdi as atom(_) = unsigned(rd) in
  let haveHWREna : bool = bitone == (CP0HWREna[rdi]) in
  if ~(haveAccessLevel | haveCU0 | haveHWREna) then
    (SignalException(ResI));
  let temp : bits(64) = match rd {
    0b00000  => EXTZ([bitzero]),  /* CPUNum */
    0b00001  => EXTZ([bitzero]),  /* SYNCI_step */
    0b00010  => EXTZ(CP0Count), /* Count */
    0b00011  => EXTZ([bitone]),   /* Count resolution */
    0b11101  => CP0UserLocal,   /* User local register */
    _        => (SignalException(ResI))
  } in
  wGPR(rt) = temp;
}

union clause ast = ERET : unit

function clause decode (0b010000 @ 0b1 @ 0b0000000000000000000 @ 0b011000) =
      Some(ERET)
function clause execute (ERET) =
      {
        checkCP0Access();
        ERETHook();
        CP0LLBit = 0b0;
        if (CP0Status.ERL() == bitone) then
          {
            nextPC = CP0ErrorEPC;
            CP0Status->ERL() = 0b0;
          }
        else
          {
            nextPC = CP0EPC;
            CP0Status->EXL() = 0b0;
          }
      }
