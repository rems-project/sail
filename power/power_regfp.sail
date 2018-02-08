(*========================================================================*)
(*                                                                        *)
(*  Copyright (c) 2015-2017 Gabriel Kerneis, Susmit Sarkar, Kathyrn Gray  *)
(*  Copyright (c) 2015-2017 Peter Sewell                                  *)
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
  [ "GPR0", "GPR1", "GPR2", "GPR3", "GPR4", "GPR5", "GPR6", "GPR7", "GPR8", "GPR9", "GPR10",
  "GPR11", "GPR12", "GPR13", "GPR14", "GPR15", "GPR16", "GPR17", "GPR18", "GPR19", "GPR20",
  "GPR21", "GPR22", "GPR23", "GPR24", "GPR25", "GPR26", "GPR27", "GPR28", "GPR29", "GPR30", "GPR31"
  ]

let (vector <0, 1024, inc, string >) SPRs =
  [ 1="XER", 8="LR", 9="CTR"(*, 256=VRSAVE (*32 bit, so not 64, caught by type checker at last*)*), 259="SPRG3", 260="SPRG4", 261="SPRG5", 262="SPRG6", 263="SPRG7"
  ]

let (vector <0, 1024, inc, string >) DCRs =
  [ 0="DCR0", 1="DCR1" ; default=undefined]

function nat length_spr i = switch i {
  case 1 -> 64
  case 8 -> 64
  case 9 -> 64
  case 259 -> 64
  case 260 -> 64
  case 261 -> 64
  case 262 -> 64
  case 263 -> 64
}

let CIA_fp = RFull("CIA")
let NIA_fp = RFull("NIA")
let mode64bit_fp = RFull("mode64bit")
let bigendianmode_fp = RFull("bigendianmode")

val ast -> (regfps,regfps,regfps,niafps,diafp,instruction_kind) effect {rreg} initial_analysis
function (regfps,regfps,regfps,niafps,diafp,instruction_kind) initial_analysis (instr) = {
  iR := [|| ||];
  oR := [|| ||];
  aR := [|| ||];
  ik := IK_simple;
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;
  switch instr {
    case (B (LI, AA, LK)) -> {
      oR := NIA_fp :: oR;
      if AA then iR := CIA_fp :: iR;
      if LK then oR := RFull("LR") :: oR;
      (bit[64]) nia' := if AA then EXTS(LI : 0b00) else CIA + EXTS(LI : 0b00);
      Nias := [|| NIAFP_concrete_address(nia') ||];
      ik := IK_branch
    }
    case (Bc (BO, BI, BD, AA, LK)) -> {
      iR := mode64bit_fp :: iR;
      iR := RFull("CTR") :: iR;
      if ~(BO[2]) then oR := RFull("CTR") :: oR;
      iR := RSliceBit("CR",BI + 32) :: iR;
      (* TODO: actually whether CIA is read and NIA written depends on runtime data *)
      (* if ctr_ok .. *)
      oR := NIA_fp :: oR;
      if AA then iR := CIA_fp :: iR; 
      Nias := [|| NIAFP_successor, NIAFP_concrete_address(if AA then EXTS(BD : 0b00) else CIA + EXTS(BD : 0b00)) ||];
      if LK then {oR := RFull("LR") :: oR; iR := CIA_fp :: iR};
      ik := IK_branch
    }
    case (Bclr (BO, BI, BH, LK)) -> {
      iR := mode64bit_fp :: iR;
      iR := RFull("CTR") :: iR;
      if ~(BO[2]) then oR := RFull("CTR") :: oR;
      iR := RSliceBit("CR",BI + 32) :: iR;
      (* TODO: actually whether LR is read, NIA written depends on runtime data *)
      (* if ctr_ok .. *) iR := RSlice("LR",0,61) :: iR;
      oR := NIA_fp :: oR;
      Nias := [|| NIAFP_successor, NIAFP_indirect_address ||];
      if LK then {oR := RFull("LR") :: oR; iR := CIA_fp :: iR;};
      ik := IK_branch;
    }
    case (Bcctr (BO, BI, BH, LK)) -> {
      iR := RSliceBit("CR",BI + 32) :: iR;
      (* TODO: actually whether CTR is read and NIA written depends on runtime data *)
      (* if cond_ok *) iR := RSlice("CTR",0,61) :: iR;
      oR := NIA_fp :: oR;
      Nias := [|| NIAFP_successor, NIAFP_indirect_address ||];
      if LK then {oR := RFull("LR") :: oR; iR := CIA_fp :: iR;};
      ik := IK_branch;
    }
    case (Crand (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Crnand (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Cror (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Crxor (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Crnor (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Creqv (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Crandc (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Crorc (BT, BA, BB)) -> {
      iR := RSliceBit("CR",BA + 32) :: RSliceBit("CR",BB + 32) :: iR;
      oR := RSliceBit("CR",BT + 32) :: oR;
    }
    case (Mcrf (BF, BFA)) -> {
      iR := RSlice("CR",4 * BFA + 32,4 * BFA + 35) :: iR;
      oR := RSlice("CR",4 * BF + 32,4 * BF + 35) :: oR;
    }
    case (Sc (LEV)) -> {
      (* fake test end instruction *)
      ();
    }
    case (Scv (LEV)) -> ()
    case (Lbz (RT, RA, D)) -> {
      if RA == 0 then () else iR := (RFull(GPRs[RA])) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lbzx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := (RFull(GPRs[RA])) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lbzu (RT, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lbzux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhz (RT, RA, D)) -> {
      if RA == 0 then () else iR := (RFull(GPRs[RA])) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhzx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhzu (RT, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhzux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lha (RT, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhax (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhau (RT, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lhaux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwz (RT, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwzx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwzu (RT, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwzux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwa (RT, RA, DS)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwax (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Lwaux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Ld (RT, RA, DS)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Ldx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Ldu (RT, RA, DS)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Ldux (RT, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Stb (RS, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stbx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stbu (RS, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stbux (RS, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR; 
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Sth (RS, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],48,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Sthx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RFull(GPRs[RB]) :: RSlice(GPRs[RS],48,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Sthu (RS, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RA]) :: oR;
      iR := RSlice(GPRs[RS],48,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Sthux (RS, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RSlice(GPRs[RS],48,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stw (RS, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stwx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stwu (RS, RA, D)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stwux (RS, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Std (RS, RA, DS)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RFull(GPRs[RS]) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stdx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RFull(GPRs[RS]) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stdu (RS, RA, DS)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RFull(GPRs[RS]) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Stdux (RS, RA, RB)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      aR := iR;
      iR := RFull(GPRs[RS]) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Lq (RTp, RA, DQ, PT)) -> {
      iR := bigendianmode_fp :: iR;
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RTp]) :: RFull(GPRs[RTp + 1]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Stq (RSp, RA, DS)) -> {
      iR := bigendianmode_fp :: iR;
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      iR := RFull(GPRs[RSp]) :: RFull(GPRs[RSp + 1]) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Lhbrx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Sthbrx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: RSlice(GPRs[RS],48,55) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Lwbrx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Stwbrx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: RSlice(GPRs[RS],48,55) :: RSlice(GPRs[RS],40,47) :: RSlice(GPRs[RS],32,39) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Ldbrx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_plain);
    }
    case (Stdbrx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      iR := RSlice(GPRs[RS],56,63) :: RSlice(GPRs[RS],48,55) :: RSlice(GPRs[RS],40,47) :: RSlice(GPRs[RS],32,39) :: RSlice(GPRs[RS],24,31) :: RSlice(GPRs[RS],16,23) :: RSlice(GPRs[RS],8,15) :: RSlice(GPRs[RS],0,7) :: iR;
      ik := IK_mem_write(Write_plain);
    }
    case (Lmw (RT, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      i := 0;
      aR := iR;
      foreach (r from RT to 31 by 1 in inc) {
        oR := RFull(GPRs[r]) :: oR;
        i := i + 32
      };
      ik := IK_mem_read(Read_plain);
    }
    case (Stmw (RS, RA, D)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      i := 0;
      foreach (r from RS to 31 by 1 in inc) {
        iR := RSlice(GPRs[r],32,63) :: iR;
        i := i + 32
      };
      ik := IK_mem_write(Write_plain);
    }
    case (Lswi (RT, RA, NB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      ([|31|]) r := 0;
      r := RT - 1;
      j := 0;
      i := 32;
      foreach (n from (if NB == 0 then 32 else NB) to 1 by 1 in dec) {
        if i == 32 then {
          r := ([|31|]) (r + 1) mod 32;
          oR := RFull(GPRs[r]) :: oR;
        };
        oR := RSlice(GPRs[r],i,i + 7) :: oR;
        j := j + 8;
        i := i + 8;
        if i == 64 then i := 32;
      };
      ik := IK_mem_read(Read_plain);
    }
    case (Lswx (RT, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: RSlice("XER",57,63) :: iR;
      aR := iR;
      (* as long as XER[57 .. 63] is unknown all registers could be written to *)
      foreach (r from 0 to 31 by 1 in inc) {oR := RFull(GPRs[r]) :: oR};
      ik := IK_mem_read(Read_plain);
    }
    case (Stswi (RS, RA, NB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      aR := iR;
      ([|31|]) r := 0;
      r := RS - 1;
      j := 0;
      i := 32;
      foreach (n from (if NB == 0 then 32 else NB) to 1 by 1 in dec) {
        if i == 32 then r := ([|32|]) (r + 1) mod 32;
        iR := RSlice(GPRs[r],i,i + 7) :: iR;
        j := j + 8;
        i := i + 8;
        if i == 64 then i := 32
      };
      ik := IK_mem_write(Write_plain);
    }
    case (Stswx (RS, RA, RB)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      ([|31|]) r := 0;
      iR := RFull(GPRs[RB]) :: RSlice("XER",57,63) :: iR;
      aR := iR;
      r := RS - 1;
      i := 32;
      ([|128|]) n_top := 0b1111111; (* maximal XER[57 .. 63]; *)
      j := 0;
      foreach (n from n_top to 1 by 1 in dec) {
        if i == 32 then r := ([|32|]) (r + 1) mod 32;
        iR := RSlice(GPRs[r],i,i + 7) :: iR;
        i := i + 8;
        j := j + 8;
        if i == 64 then i := 32
      };
      ik := IK_mem_write(Write_plain);
    }
    case (Addi (RT, RA, SI)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Addis (RT, RA, SI)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Add (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Subf (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Addic (RT, RA, SI)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: RField("XER","CA") :: oR;
    }
    case (AddicDot (RT, RA, SI)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: RField("XER","CA") :: oR;
      iR := RField("XER","SO") :: iR;
      oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
    }
    case (Subfic (RT, RA, SI)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: RField("XER","CA") :: oR;
    }
    case (Addc (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Subfc (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Adde (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      iR := RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Subfe (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      iR := RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Addme (RT, RA, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Subfme (RT, RA, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Addze (RT, RA, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Subfze (RT, RA, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RField("XER","CA") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Neg (RT, RA, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Mulli (RT, RA, SI)) -> {
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Mullw (RT, RA, RB, OE, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Mulhw (RT, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR;
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Mulhwu (RT, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR; 
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Divw (RT, RA, RB, OE, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR;
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divwu (RT, RA, RB, OE, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR;
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divwe (RT, RA, RB, OE, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR;
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divweu (RT, RA, RB, OE, Rc)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
      oR := RSlice(GPRs[RT],32,63) :: RSlice(GPRs[RT],0,31) :: oR;
      if Rc then {
        iR := mode64bit_fp :: iR;
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Mulld (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Mulhd (RT, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Mulhdu (RT, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Divd (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divdu (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divde (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Divdeu (RT, RA, RB, OE, Rc)) -> {
      iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      if OE then {
        iR := RField("XER","SO") :: iR;                   (* set_SO_OV *)
        oR := RField("XER","OV") :: RField("XER","SO") :: oR; (* set_SO_OV *)
      }
    }
    case (Cmpi (BF, L, RA, SI)) -> {
      iR := (if L == 0 then RSlice(GPRs[RA],32,63) else RFull(GPRs[RA])) :: iR;
      iR := RField("XER","SO") :: iR;
      oR := RSlice("CR",4 * BF + 32,4 * BF + 35) :: oR;
    }
    case (Cmp (BF, L, RA, RB)) -> {
      if L == 0 then
        iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR
      else iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      iR := RField("XER","SO") :: iR;
      oR := RSlice("CR",4 * BF,4 * BF + 35) :: oR;
    }
    case (Cmpli (BF, L, RA, UI)) -> {
      iR := (if L == 0 then RSlice(GPRs[RA],32,63) else RFull(GPRs[RA])) :: iR;
      iR := RField("XER","SO") :: iR;
      oR := RSlice("CR",4 * BF + 32,4 * BF + 35) :: oR;
    }
    case (Cmpl (BF, L, RA, RB)) -> {
      if L == 0 then
        iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR
      else
        iR := RFull(GPRs[RA]) :: RFull(GPRs[RB]) :: iR;
      iR := RField("XER","SO") :: iR;
      oR := RSlice("CR",4 * BF + 32,4 * BF + 35) :: oR;
    }
(*    case (Twi (TO, RA, SI)) -> {
      iR := RSlice(GPRs[RA],32,63) :: iR;
    }
    case (Tw (TO, RA, RB)) -> {
      iR := RSlice(GPRs[RA],32,63) :: RSlice(GPRs[RB],32,63) :: iR;
    }
    case (Tdi (TO, RA, SI)) -> ()
    case (Td (TO, RA, RB)) -> () *)
    case (Isel (RT, RA, RB, BC)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RSliceBit("CR",BC + 32) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Andi (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: RField("XER","SO") :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)  
    }
    case (Andis (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: RField("XER","SO") :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)  
    }
    case (Ori (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (Oris (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (Xori (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (Xoris (RS, RA, UI)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (And (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Xor (RS, RA, RB, Rc)) -> {
      if RS == RB then {
        iR := RFull(GPRs[RS]) :: iR;
        oR := RFull(GPRs[RA]) :: oR;
      }
      else {
        iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
        oR := RFull(GPRs[RA]) :: oR;
      };
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Nand (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Or (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Nor (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Eqv (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Andc (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Orc (RS, RA, RB, Rc)) -> {
      iR := RFull(GPRs[RS]) :: RFull(GPRs[RB]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Extsb (RS, RA, Rc)) -> {
      iR := RSliceBit(GPRs[RS],56) :: iR;
      iR := RSlice(GPRs[RS],56,63) :: iR;
      oR := RSlice(GPRs[RA],56,63) :: oR;
      oR := RSlice(GPRs[RA],0,55) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Extsh (RS, RA, Rc)) -> {
      iR := RSliceBit(GPRs[RS],48) :: iR;
      iR := RSlice(GPRs[RS],48,63) :: iR;
      oR := RSlice(GPRs[RA],48,63) :: oR;
      oR := RSlice(GPRs[RA],0,47) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Cntlzw (RS, RA, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      }
    }
    case (Cmpb (RS, RA, RB)) -> {
      foreach (n from 0 to 7 by 1 in inc) {
        iR := RSlice(GPRs[RS],8 * n,8 * n + 7) :: RSlice(GPRs[RB],8 * n,8 * n + 7) :: iR;
        oR := RSlice(GPRs[RA],8 * n,8 * n + 7) :: oR;
      }
    }
    case (Popcntb (RS, RA)) -> {
      foreach (i from 0 to 7 by 1 in inc) {
        foreach (j from 0 to 7 by 1 in inc) iR := RSliceBit(GPRs[RS],i * 8 + j) :: iR;
        oR := RSlice(GPRs[RA],i * 8,i * 8 + 7) :: oR;
      }
    }
    case (Popcntw (RS, RA)) -> {
      foreach (i from 0 to 1 by 1 in inc) {
        foreach (j from 0 to 31 by 1 in inc) iR := RSliceBit(GPRs[RS],i * 32 + j) :: iR;
        oR := RSlice(GPRs[RA],i * 32,i * 32 + 31) :: oR;
      }
    }
    case (Prtyd (RS, RA)) -> {
      foreach (i from 0 to 7 by 1 in inc) iR := RSliceBit(GPRs[RS],i * 8 + 7) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (Prtyw (RS, RA)) -> {
      foreach (i from 0 to 3 by 1 in inc) iR := RSliceBit(GPRs[RS],i * 8 + 7) :: iR;
      foreach (i from 4 to 7 by 1 in inc) iR := RSliceBit(GPRs[RS],i * 8 + 7) :: iR;
      oR := RSlice(GPRs[RA],0,31) :: oR;
      oR := RSlice(GPRs[RA],32,63) :: oR;
    }
    case (Extsw (RS, RA, Rc)) -> {
      iR := RSliceBit(GPRs[RS],32) :: iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RFull(GPRs[RA]) :: oR;
    }
    case (Cntlzd (RS, RA, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Popcntd (RS, RA)) -> {
      foreach (i from 0 to 63 by 1 in inc) iR := RSliceBit(GPRs[RS],i) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
    }
    (* TODO: here the footprint depends on dynamic data *)
    case (Bpermd (RS, RA, RB)) -> {
      foreach (i from 0 to 7 by 1 in inc) {
        iR := RSlice(GPRs[RS],8 * i,8 * i + 7) :: iR;
        iR := RFull(GPRs[RB]) :: iR; (* this is actually only a single bit, *)
                                 (* which one it is depends on the read before *)
        oR := RFull(GPRs[RA]) :: oR;
      }
    }
    case (Rlwinm (RS, RA, SH, MB, ME, Rc)) -> {
      iR := RSlice(GPRs[RS],32,63) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rlwnm (RS, RA, RB, MB, ME, Rc)) -> {
      iR := RSlice(GPRs[RB],59,63) :: RSlice(GPRs[RS],32,63) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rlwimi (RS, RA, SH, MB, ME, Rc)) -> {
      iR := RSlice(GPRs[RS],32,63) :: iR;
      iR := RFull(GPRs[RA]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldicl (RS, RA, sh, mb, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldicr (RS, RA, sh, me, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldic (RS, RA, sh, mb, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldcl (RS, RA, RB, mb, Rc)) -> {
      iR := RSlice(GPRs[RB],58,63) :: iR;
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldcr (RS, RA, RB, me, Rc)) -> {
      iR := RSlice(GPRs[RB],58,63) :: iR;
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Rldimi (RS, RA, sh, mb, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Slw (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],59,63) :: iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      iR := RSliceBit(GPRs[RB],58) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Srw (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],59,63) :: iR;
      iR := RSlice(GPRs[RS],32,63) :: iR;
      iR := RSliceBit(GPRs[RB],58) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };      
    }
    case (Srawi (RS, RA, SH, Rc)) -> {
      iR := RSlice(GPRs[RS],32,63) :: iR;
      iR := RSliceBit(GPRs[RS],32) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
    }
    case (Sraw (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],59,63) :: iR;
      iR := RSlice(GPRs[RS],32,63) :: RSliceBit(GPRs[RB],58) :: RSliceBit(GPRs[RS],32) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
    }
    case (Sld (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],58,63) :: RFull(GPRs[RS]) :: iR;
      iR := RSliceBit(GPRs[RB],57) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Srd (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],58,63) :: RFull(GPRs[RS]) :: iR;
      iR := RSliceBit(GPRs[RB],57) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
    }
    case (Sradi (RS, RA, sh, Rc)) -> {
      iR := RFull(GPRs[RS]) :: iR;
      iR := RSliceBit(GPRs[RS],0) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
    }
    case (Srad (RS, RA, RB, Rc)) -> {
      iR := RSlice(GPRs[RB],58,63) :: RFull(GPRs[RS]) :: RSliceBit(GPRs[RB],57) :: RSliceBit(GPRs[RS],0) :: iR;
      oR := RFull(GPRs[RA]) :: oR;
      if Rc then {
        iR := RField("XER","SO") :: iR;
        oR := RField("CR","CR0") :: oR; (* set_overflow_cr0 *)
      };
      oR := RField("XER","CA") :: oR;
    }
    case (Cdtbcd (RS, RA)) -> {
      foreach (i from 0 to 1 by 1 in inc) {
        n := i * 32;
        iR := RSlice(GPRs[RS],n + 12,n + 31) :: iR;
        oR := RSlice(GPRs[RA],n + 0,n + 31) :: oR;
      }
    }
    case (Cbcdtd (RS, RA)) -> {
      foreach (i from 0 to 1 by 1 in inc) {
        n := i * 32;
        iR := RSlice(GPRs[RS],n + 8,n + 31) :: iR;
        oR := RSlice(GPRs[RA],n + 0,n + 31) :: oR;
      }
    }
    case (Addg6s (RT, RA, RB)) -> {
      foreach (i from 0 to 15 by 1 in inc) {
        iR := RSlice(GPRs[RA],4 * i,63) :: iR;
        iR := RSlice(GPRs[RB],4 * i,63) :: iR;
      };
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Mtspr (RS, spr)) -> {
      n := spr[5 .. 9] : spr[0 .. 4];
      if n == 1 then {
        iR := RFull(GPRs[RS]) :: iR;
        oR := RFull("XER") :: oR;
      }
      else {
        (* the below is debatable: to determine the length of that register, does it
         * really need to read the content? *)
        iR := RFull(SPRs[n]) ::iR; 
        if length_spr(n) == 64 then {
          iR := RFull(GPRs[RS]) :: iR;
          oR := RFull(SPRs[n]) :: oR;
        }
        else if n == 152 then {
          iR := RSlice(GPRs[RS],32,63) :: iR;
          oR := RFull("CTRL") :: oR;
        }
        else ();
      }
    }
    case (Mfspr (RT, spr)) -> {
      n := spr[5 .. 9] : spr[0 .. 4];
      iR := RFull(SPRs[n]) :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Mtcrf (RS, FXM)) -> {
      iR := RFull("CR") :: RSlice(GPRs[RS],32,63) :: iR;
      oR := RFull("CR") :: oR;
    }
    case (Mfcr (RT)) -> {
      iR := RFull("CR") :: iR;
      oR := RFull(GPRs[RT]) :: oR;
    }
    case (Mtocrf (RS, FXM)) -> {
      ([|7|]) n := 0;
      count := 0;
      foreach (i from 0 to 7 by 1 in inc)
      if FXM[i] == 1
      then {
        n := i;
        count := count + 1
      }
      else ();
      if count == 1
      then {
        oR := RSlice("CR",4 * n + 32,4 * n + 35) :: oR;
        iR := RSlice(GPRs[RS],4 * n + 32,4 * n + 35) :: iR;
      }
      else oR := RFull("CR") :: oR;
    }
    case (Mfocrf (RT, FXM)) -> {
      ([|7|]) n := 0;
      count := 0;
      foreach (i from 0 to 7 by 1 in inc)
      if FXM[i] == 1
      then {
        n := i;
        count := count + 1
      }
      else ();
      if count == 1
      then {
        iR := RSlice("CR",4 * n + 32,4 * n + 35) :: iR;
        oR := RFull(GPRs[RT]) :: oR;
      }
      else oR := RFull(GPRs[RT]) :: oR;
    }
    case (Mcrxr (BF)) -> {
      iR := RSlice("XER",32,35) :: iR;
      oR := RSlice("CR",4 * BF + 32,4 * BF + 35) :: RSlice("XER",32,35) :: oR;
    }
    case (Dlmzb (RS, RA, RB, Rc)) -> ()
    case (Macchws (RT, RA, RB, OE, Rc)) -> ()
    case (Macchwu (RT, RA, RB, OE, Rc)) -> ()
    case (Macchwsu (RT, RA, RB, OE, Rc)) -> ()
    case (Machhws (RT, RA, RB, OE, Rc)) -> ()
    case (Machhwu (RT, RA, RB, OE, Rc)) -> ()
    case (Machhwsu (RT, RA, RB, OE, Rc)) -> ()
    case (Maclhw (RT, RA, RB, OE, Rc)) -> ()
    case (Maclhws (RT, RA, RB, OE, Rc)) -> ()
    case (Maclhwu (RT, RA, RB, OE, Rc)) -> ()
    case (Maclhwsu (RT, RA, RB, OE, Rc)) -> ()
    case (Mulchw (RT, RA, RB, Rc)) -> ()
    case (Mulchwu (RT, RA, RB, Rc)) -> ()
    case (Mulhhw (RT, RA, RB, Rc)) -> ()
    case (Mulhhwu (RT, RA, RB, Rc)) -> ()
    case (Mullhw (RT, RA, RB, Rc)) -> ()
    case (Mullhwu (RT, RA, RB, Rc)) -> ()
    case (Nmacchw (RT, RA, RB, OE, Rc)) -> ()
    case (Nmacchws (RT, RA, RB, OE, Rc)) -> ()
    case (Nmachhw (RT, RA, RB, OE, Rc)) -> ()
    case (Nmachhws (RT, RA, RB, OE, Rc)) -> ()
    case (Nmaclhw (RT, RA, RB, OE, Rc)) -> ()
    case (Nmaclhws (RT, RA, RB, OE, Rc)) -> ()
    case (Icbi (RA, RB)) -> ()
    case (Icbt (CT, RA, RB)) -> ()
    case (Dcba (RA, RB)) -> ()
    case (Dcbt (TH, RA, RB)) -> ()
    case (Dcbtst (TH, RA, RB)) -> ()
    case (Dcbz (RA, RB)) -> ()
    case (Dcbst (RA, RB)) -> ()
    case (Dcbf (L, RA, RB)) -> ()
    case Isync -> {
      ik := IK_barrier(Barrier_Isync);
    }
    case (Lbarx (RT, RA, RB, EH)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_reserve);
    }
    case (Lharx (RT, RA, RB, EH)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_reserve);
    }
    case (Lwarx (RT, RA, RB, EH)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_reserve);
    }
    case (Stbcx (RS, RA, RB)) -> {
      ik := IK_mem_write(Write_conditional);
    }
    case (Sthcx (RS, RA, RB)) -> {
      ik := IK_mem_write(Write_conditional);
    }
    case (Stwcx (RS, RA, RB)) -> {
      ik := IK_mem_write(Write_conditional);
    }
    case (Ldarx (RT, RA, RB, EH)) -> {
      if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
      iR := RFull(GPRs[RB]) :: iR;
      aR := iR;
      oR := RFull(GPRs[RT]) :: oR;
      ik := IK_mem_read(Read_reserve);
    }
    case (Stdcx (RS, RA, RB)) -> {
      ik := IK_mem_write(Write_conditional);
    }
    case (Sync (L)) -> {
      ik := switch L {
        case 0b00 -> { IK_barrier(Barrier_Sync) }
        case 0b01 -> { IK_barrier(Barrier_LwSync) }
      }
    }
    case Eieio -> {
      ik := IK_barrier(Barrier_Eieio)
    }
    case (Wait (WC)) -> ()
  };
  (iR,oR,aR,Nias,Dia,ik)
}

val ast -> (regfps,regfps,regfps,niafps,diafp,instruction_kind) effect {rreg} recalculate_lswx_reg_footprint
(* run when footprint transition is taken, supplying n_top = XER[57 .. 63] as a parameter *)
function (regfps,regfps,regfps,niafps,diafp,instruction_kind) recalculate_lswx_reg_footprint instr = {
  (regfps) iR := [|| ||];
  (regfps) oR := [|| ||];
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;
  ik := IK_mem_read(Read_plain);
  let (RT,RA,RB) = switch instr {case (Lswx (RT, RA, RB)) -> (RT,RA,RB)} in {
  if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
  ([|31|]) r := 0;
  iR := RFull(GPRs[RB]) :: RSlice("XER",57,63) :: iR;
  aR := iR;
  r := RT - 1;
  i := 32;
  ([|128|]) n_top := XER[57 .. 63];
  if n_top == 0 then
    oR := RFull(GPRs[RT]) :: oR
  else {
    j := 0;
    n_r := n_top quot 4;
    n_mod := n_top mod 4;
    n_r := if n_mod == 0 then n_r else n_r + 1;
    foreach (n from n_r to 1 by 1 in dec) {
      r := ([|32|]) (r + 1) mod 32;
      j := j + 32;
      oR := RFull(GPRs[r]) :: oR
    }
  };
  (iR,oR,aR,Nias,Dia,ik)}
}

val ast -> (regfps,regfps,regfps,niafps,diafp,instruction_kind) effect {rreg} recalculate_stswx_reg_footprint
(* run when footprint transition is taken, supplying n_top = XER[57 .. 63] as a parameter *)
function (regfps,regfps,regfps,niafps,diafp,instruction_kind) recalculate_stswx_reg_footprint instr = {
  (regfps) iR := [|| ||];
  (regfps) oR := [|| ||];
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;
  ik := IK_mem_write(Write_plain);
  let (RS,RA,RB) = switch instr {case (Stswx (RS, RA, RB)) -> (RS,RA,RB)} in {
  if RA == 0 then () else iR := RFull(GPRs[RA]) :: iR;
  ([|31|]) r := 0;
  iR := RFull(GPRs[RB]) :: RSlice("XER",57,63) :: iR;
  aR := iR;
  r := RS - 1;
  i := 32;
  ([|128|]) n_top := XER[57 .. 63];
  j := 0;
  foreach (n from n_top to 1 by 1 in dec) {
    if i == 32 then r := ([|32|]) (r + 1) mod 32;
    iR := RSlice(GPRs[r],i,i + 7) :: iR;
    i := i + 8;
    j := j + 8;
    if i == 64 then i := 32
  };
  ik := IK_mem_write(Write_plain);
  (iR,oR,aR,Nias,Dia,ik)}
}
