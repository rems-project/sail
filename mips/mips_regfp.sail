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

let (vector <0, 32, inc, string >) GPRs =
  [ "GPR00", "GPR01", "GPR02", "GPR03", "GPR04", "GPR05", "GPR06", "GPR07", "GPR08", "GPR09", "GPR10",
  "GPR11", "GPR12", "GPR13", "GPR14", "GPR15", "GPR16", "GPR17", "GPR18", "GPR19", "GPR20",
  "GPR21", "GPR22", "GPR23", "GPR24", "GPR25", "GPR26", "GPR27", "GPR28", "GPR29", "GPR30", "GPR31"
  ]

let CIA_fp = RFull("CIA")
let NIA_fp = RFull("NIA")

function (regfps,regfps,regfps,niafps,diafp,instruction_kind) initial_analysis (instr) = {
  iR := [|| ||];
  oR := [|| ||];
  aR := [|| ||];
  ik := IK_simple;
  Nias := [|| ||];
  Dia := DIAFP_none;

  switch instr {
    case (DADDIU (rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (DADDU (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DADDI (rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (DADD (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (ADD(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (ADDI(rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (ADDU(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (ADDIU(rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (DSUBU (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSUB (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SUB(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SUBU(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (AND (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (ANDI (rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (OR (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (ORI (rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (NOR (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (XOR (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (XORI (rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (LUI (rt, imm)) -> {
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (DSLL (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSLL32 (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSLLV (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRA (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRA32 (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRAV (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRL (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRL32 (rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (DSRLV (rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SLL(rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SLLV(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SRA(rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SRAV(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SRL(rt, rd, sa)) -> {
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SRLV(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SLT(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SLTI(rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (SLTU(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (SLTIU(rs, rt, imm)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (MOVN(rs, rt, rd)) -> {
      (* XXX don't always write rd *)
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (MOVZ(rs, rt, rd)) -> {
      (* XXX don't always write rd *)
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (MFHI(rd)) -> {
      iR := RFull("HI") :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (MFLO(rd)) -> {
      iR := RFull("LO") :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (MTHI(rs)) -> {
      oR := RFull("HI") :: oR;
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
    }
    case (MTLO(rs)) -> {
      oR := RFull("LO") :: oR;
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
    }
    case (MUL(rs, rt, rd)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      if rd == 0 then () else oR := RFull(GPRs[rd]) :: oR;
    }
    case (MULT(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (MULTU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DMULT(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DMULTU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (MADD(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      iR := RFull("HI") :: RFull ("LO") :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (MADDU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      iR := RFull("HI") :: RFull ("LO") :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (MSUB(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      iR := RFull("HI") :: RFull ("LO") :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (MSUBU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      iR := RFull("HI") :: RFull ("LO") :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DIV(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DIVU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DDIV(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (DDIVU(rs, rt)) -> {
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
      oR := RFull("HI") :: RFull ("LO") :: oR;
    }
    case (J(offset)) -> {
      ik := IK_branch;
      Dia := DIAFP_concrete((PC + 4)[63..28] : offset : 0b00);
    }
    case (JAL(offset)) -> {
      ik := IK_branch;
      oR := RFull("GPR31") :: oR;
      Dia := DIAFP_concrete((PC + 4)[63..28] : offset : 0b00);
    }
    case (JR(rs)) -> {
      ik := IK_branch;
      iR := RFull(GPRs[rs]) :: iR;
      Dia := DIAFP_reg(RFull(GPRs[rs]));
    }
    case (JALR(rs, rd)) -> {
      ik := IK_branch;
      iR := RFull(GPRs[rs]) :: iR;
      oR := RFull("GPR31") :: oR;
      Dia := DIAFP_reg(RFull(GPRs[rs]));
    }
    case (BEQ(rs, rd, imm, ne, likely)) -> {
      ik := IK_branch;
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if rd == 0 then () else iR := RFull(GPRs[rd]) :: iR;
      let (bit[64]) offset = (EXTS(imm : 0b00) + 4) in
      Dia := DIAFP_concrete (PC + offset);
    }
    case (BCMPZ(rs, imm, cmp, link, likely)) -> {
      ik := IK_branch;
      if rs == 0 then () else iR := RFull(GPRs[rs]) :: iR;
      if link then
        oR := RFull("GPR31") :: oR;
      let (bit[64]) offset = (EXTS(imm : 0b00) + 4) in
      Dia := DIAFP_concrete (PC + offset);
    }
    case (SYSCALL_THREAD_START) -> ()
(*

    case (SYSCALL) =
    case (BREAK) =
    case (WAIT) = {
    case (TRAPREG(rs, rt, cmp)) =
    case (TRAPIMM(rs, imm, cmp)) =
*)
    case (Load(width, signed, linked, base, rt, offset)) -> {
      ik := IK_mem_read (if linked then Read_reserve else Read_plain);
      if linked then oR := RFull("CP0LLBit")::RFull("CP0LLAddr")::oR else ();
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (Store(width, conditional, base, rt, offset)) -> {
      ik := IK_mem_write(if conditional then Write_conditional else Write_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if conditional then iR := RFull("CP0LLBit")::iR else ();
      if (conditional & (rt != 0)) then oR := RFull(GPRs[rt])::oR else ();
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
    }
    case (LWL(base, rt, offset)) -> {
      ik := IK_mem_read(Read_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (LWR(base, rt, offset)) -> {
      ik := IK_mem_read(Read_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (SWL(base, rt, offset)) -> {
      ik := IK_mem_write(Write_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
    }
    case (SWR(base, rt, offset)) -> {
      ik := IK_mem_write(Write_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
    }
    case (LDL(base, rt, offset)) -> {
      ik := IK_mem_read(Read_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (LDR(base, rt, offset)) -> {
      ik := IK_mem_read(Read_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else oR := RFull(GPRs[rt]) :: oR;
    }
    case (SDL(base, rt, offset)) -> {
      ik := IK_mem_write(Write_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
    }
    case (SDR(base, rt, offset)) -> {
      ik := IK_mem_write(Write_plain);
      if base == 0 then () else aR := RFull(GPRs[base]) :: aR;
      iR := aR;
      if rt == 0 then () else iR := RFull(GPRs[rt]) :: iR;
    }
(*
    case (CACHE(base, op, imm)) =
    case (PREF(base, op, imm)) =
*)
    case (SYNC) -> {
      iK := IK_barrier(Barrier_MIPS_SYNC);
    }
(*
    case (MFC0(rt, rd, sel, double))
    case (HCF)
    case (MTC0(rt, rd, sel, double))
    case (TLBWI) 
    case (TLBWR) 
    case (TLBR) 
    case ((TLBP)) 
    case (RDHWR(rt, rd)) 
    case (ERET) 
*)
  };
  (iR,oR,aR,Nias,Dia,ik)
}
