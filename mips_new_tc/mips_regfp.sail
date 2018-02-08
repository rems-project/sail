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

let GPRs : vector <0, 32, inc, string > =
  [ "GPR00", "GPR01", "GPR02", "GPR03", "GPR04", "GPR05", "GPR06", "GPR07", "GPR08", "GPR09", "GPR10",
  "GPR11", "GPR12", "GPR13", "GPR14", "GPR15", "GPR16", "GPR17", "GPR18", "GPR19", "GPR20",
  "GPR21", "GPR22", "GPR23", "GPR24", "GPR25", "GPR26", "GPR27", "GPR28", "GPR29", "GPR30", "GPR31"
  ]

let CIA_fp = RFull("CIA")
let NIA_fp = RFull("NIA")

function (regfps,regfps,regfps,niafps,diafp,instruction_kind) initial_analysis ((ast) instr) = {
  (regfps) iR = [|| ||];
  (regfps) oR = [|| ||];
  (regfps) aR = [|| ||];
  (instruction_kind) ik = IK_simple;
  (niafps) Nias = [|| ||];
  (diafp) Dia = DIAFP_none;

  switch instr {
    (DADDIU (rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (DADDU (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DADDI (rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (DADD (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (ADD(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (ADDI(rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (ADDU(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (ADDIU(rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (DSUBU (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSUB (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SUB(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SUBU(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (AND (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (ANDI (rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (OR (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (ORI (rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (NOR (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (XOR (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (XORI (rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (LUI (rt, imm))  => {
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (DSLL (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSLL32 (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSLLV (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRA (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRA32 (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRAV (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRL (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRL32 (rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (DSRLV (rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SLL(rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SLLV(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SRA(rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SRAV(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SRL(rt, rd, sa))  => {
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SRLV(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SLT(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SLTI(rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (SLTU(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (SLTIU(rs, rt, imm))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (MOVN(rs, rt, rd))  => {
      /* XXX don't always write rd */
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (MOVZ(rs, rt, rd))  => {
      /* XXX don't always write rd */
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (MFHI(rd))  => {
      iR = RFull("HI") :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (MFLO(rd))  => {
      iR = RFull("LO") :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (MTHI(rs))  => {
      oR = RFull("HI") :: oR;
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
    }
    (MTLO(rs))  => {
      oR = RFull("LO") :: oR;
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
    }
    (MUL(rs, rt, rd))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR = RFull(GPRs[rd]) :: oR;
    }
    (MULT(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (MULTU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DMULT(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DMULTU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (MADD(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      iR = RFull("HI") :: RFull ("LO") :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (MADDU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      iR = RFull("HI") :: RFull ("LO") :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (MSUB(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      iR = RFull("HI") :: RFull ("LO") :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (MSUBU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      iR = RFull("HI") :: RFull ("LO") :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DIV(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DIVU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DDIV(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (DDIVU(rs, rt))  => {
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
      oR = RFull("HI") :: RFull ("LO") :: oR;
    }
    (J(offset))  => {
      /* XXX actually unconditional jump */
      /*ik = IK_cond_branch;*/
      Dia = DIAFP_concrete((PC + 4)[63..28] : offset : 0b00);
    }
    (JAL(offset))  => {
      /* XXX actually unconditional jump */
      /*ik = IK_cond_branch;*/
      oR = RFull("GPR31") :: oR;
      Dia = DIAFP_concrete((PC + 4)[63..28] : offset : 0b00);
    }
    (JR(rs))  => {
      /* XXX actually unconditional jump */
      /*ik = IK_cond_branch;*/
      iR = RFull(GPRs[rs]) :: iR;
      Dia = DIAFP_reg(RFull(GPRs[rs]));
    }
    (JALR(rs, rd))  => {
      /* XXX actually unconditional jump */
      /*ik = IK_cond_branch;*/
      iR = RFull(GPRs[rs]) :: iR;
      oR = RFull("GPR31") :: oR;
      Dia = DIAFP_reg(RFull(GPRs[rs]));
    }
    (BEQ(rs, rd, imm, ne, likely))  => {
      ik = IK_cond_branch;
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if rd == 0 then () else iR = RFull(GPRs[rd]) :: iR;
      let offset : bits(64) = (EXTS(imm : 0b00) + 4) in
      Dia = DIAFP_concrete (PC + offset);
    }
    (BCMPZ(rs, imm, cmp, link, likely))  => {
      ik = IK_cond_branch;
      if rs == 0 then () else iR = RFull(GPRs[rs]) :: iR;
      if link then
        oR = RFull("GPR31") :: oR;
      let offset : bits(64) = (EXTS(imm : 0b00) + 4) in
      Dia = DIAFP_concrete (PC + offset);
    }
    (SYSCALL_THREAD_START)  => ()
/*

    case (SYSCALL) =
    case (BREAK) =
    case (WAIT) = {
    case (TRAPREG(rs, rt, cmp)) =
    case (TRAPIMM(rs, imm, cmp)) =
*/
    (Load(width, signed, linked, base, rt, offset))  => {
      ik = IK_mem_read (if linked then Read_reserve else Read_plain);
      if linked then oR = RFull("CP0LLBit")::RFull("CP0LLAddr")::oR else ();
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (Store(width, conditional, base, rt, offset))  => {
      ik = IK_mem_write(if conditional then Write_conditional else Write_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if conditional then iR = RFull("CP0LLBit")::iR else ();
      if (conditional & (rt != 0)) then oR = RFull(GPRs[rt])::oR else ();
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
    }
    (LWL(base, rt, offset))  => {
      ik = IK_mem_read(Read_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (LWR(base, rt, offset))  => {
      ik = IK_mem_read(Read_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (SWL(base, rt, offset))  => {
      ik = IK_mem_write(Write_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
    }
    (SWR(base, rt, offset))  => {
      ik = IK_mem_write(Write_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
    }
    (LDL(base, rt, offset))  => {
      ik = IK_mem_read(Read_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (LDR(base, rt, offset))  => {
      ik = IK_mem_read(Read_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else oR = RFull(GPRs[rt]) :: oR;
    }
    (SDL(base, rt, offset))  => {
      ik = IK_mem_write(Write_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
    }
    (SDR(base, rt, offset))  => {
      ik = IK_mem_write(Write_plain);
      if base == 0 then () else aR = RFull(GPRs[base]) :: aR;
      iR = aR;
      if rt == 0 then () else iR = RFull(GPRs[rt]) :: iR;
    }
/*
    case (CACHE(base, op, imm)) =
    case (PREF(base, op, imm)) =
*/
    (SYNC)  => {
      iK = IK_barrier(Barrier_MIPS_SYNC);
    }
/*
    case (MFC0(rt, rd, sel, double))
    case (HCF)
    case (MTC0(rt, rd, sel, double))
    case (TLBWI) 
    case (TLBWR) 
    case (TLBR) 
    case ((TLBP)) 
    case (RDHWR(rt, rd)) 
    case (ERET) 
*/
  };
  (iR,oR,aR,Nias,Dia,ik)
}
