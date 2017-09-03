let (vector <0, 32, inc, string >) GPRstr =
  [ "x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10",
  "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18", "x19", "x20",
  "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "x30", "x31"
  ]

let CIA_fp = RFull("CIA")
let NIA_fp = RFull("NIA")

function (regfps,regfps,regfps,niafps,diafp,instruction_kind) initial_analysis (instr) = {
  iR := [|| ||];
  oR := [|| ||];
  aR := [|| ||];
  ik := IK_simple;
  Nias := [|| NIAFP_successor ||];
  Dia := DIAFP_none;

  switch instr {
     case (EBREAK) -> ()
     case (UTYPE ( imm, rd, op)) -> {
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (JAL ( imm, rd)) -> {
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
            let (bit[64]) offset = EXTS(imm) in
            Nias := [|| NIAFP_concrete_address (PC + offset) ||]
     }
     case (JALR ( imm, rs, rd)) -> {
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
            let (bit[64]) offset = EXTS(imm) in
            Nias := [|| NIAFP_register (RFull(GPRstr[rs])) ||];
     }
     case (BTYPE ( imm, rs2, rs1, op)) -> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            ik := IK_cond_branch;
            let (bit[64]) offset = EXTS(imm) in
            Nias := NIAFP_concrete_address(PC + offset) :: Nias;
     }
     case (ITYPE ( imm, rs, rd, op)) -> {
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (SHIFTIOP ( imm, rs, rd, op)) -> {
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (RTYPE ( rs2, rs1, rd, op)) -> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (LOAD ( imm, rs, rd, unsign, width, aq, rl)) -> { (* XXX "unsigned" causes name conflict in lem shallow embedding... *)
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
            aR := iR;
            ik :=
              switch (aq, rl) {
                case (false, false) -> IK_mem_read (Read_plain)
                case (true,  false) -> IK_mem_read (Read_RISCV_acquire)
                case (false, true)  -> exit "not implemented"
                case (true,  true)  -> IK_mem_read (Read_RISCV_strong_acquire)
              };
     }
     case (STORE( imm, rs2, rs1, width, aq, rl)) -> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rs1 == 0) then () else aR := RFull(GPRstr[rs1]) :: aR;
            ik :=
              switch (aq, rl) {
                case (false, false) -> IK_mem_write (Write_plain)
                case (true,  false) -> exit "not implemented"
                case (false, true)  -> IK_mem_write (Write_RISCV_release)
                case (true,  true)  -> IK_mem_write (Write_RISCV_strong_release)
              };
     }
     case (ADDIW ( imm, rs, rd)) -> {
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (SHIFTW ( imm, rs, rd, op)) -> {
            if (rs == 0) then () else iR := RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     } 
     case (RTYPEW ( rs2, rs1, rd, op))-> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
     }
     case (FENCE(pred, succ)) -> {
            ik :=
              switch(pred, succ) {
                case (0b0011, 0b0011) -> IK_barrier (Barrier_RISCV_rw_rw)
                case (0b0010, 0b0011) -> IK_barrier (Barrier_RISCV_r_rw)
                case (0b0011, 0b0001) -> IK_barrier (Barrier_RISCV_rw_w)
                case (0b0001, 0b0001) -> IK_barrier (Barrier_RISCV_w_w)
                case _ -> exit "not implemented"
              };
     }
     case (FENCEI) -> {
            ik := IK_barrier (Barrier_RISCV_i);
     }
     case (LOADRES ( aq, rl, rs1, width, rd)) -> {
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;
            aR := iR;
            ik := switch (aq, rl) {
              case (false, false) -> IK_mem_read (Read_RISCV_reserved)
              case (true,  false) -> IK_mem_read (Read_RISCV_reserved_acquire)
              case (false, true)  -> exit "not implemented"
              case (true,  true)  -> IK_mem_read (Read_RISCV_reserved_strong_acquire)
            };
     }
     case (STORECON( aq, rl, rs2, rs1, width, rd)) -> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rs1 == 0) then () else aR := RFull(GPRstr[rs1]) :: aR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;

            ik := switch (aq, rl) {
              case (false, false) -> IK_mem_write (Write_RISCV_conditional)
              case (false, true)  -> IK_mem_write (Write_RISCV_conditional_release)
              case (true,  _)     -> exit "not implemented"
            };
     }
     case (AMO( op, aq, rl, rs2, rs1, width, rd)) -> {
            if (rs2 == 0) then () else iR := RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR := RFull(GPRstr[rs1]) :: iR;
            if (rs1 == 0) then () else aR := RFull(GPRstr[rs1]) :: aR;
            if (rd == 0) then () else oR := RFull(GPRstr[rd]) :: oR;

            ik := switch (aq, rl) {
              case (false, false) -> IK_mem_rmw (Read_RISCV_reserved, Write_RISCV_conditional)
              case (false, true)  -> IK_mem_rmw (Read_RISCV_reserved, Write_RISCV_conditional_release)
              case (true,  false) -> IK_mem_rmw (Read_RISCV_reserved_acquire,
                                                                      Write_RISCV_conditional)
              case (true,  true)  -> IK_mem_rmw (Read_RISCV_reserved_strong_acquire,
                                                                      Write_RISCV_conditional_strong_release)
            };
     }
  };
  (iR,oR,aR,Nias,Dia,ik)
}
