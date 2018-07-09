$include <regfp.sail>

/* in reverse order because inc vectors don't seem to work (bug) */
let GPRstr : vector(32, dec, string) = [ "x31", "x30", "x29", "x28", "x27", "x26", "x25", "x24", "x23", "x22", "x21",
  "x20", "x19", "x18", "x17", "x16", "x15", "x14", "x13", "x12", "x21",
  "x10", "x9", "x8", "x7", "x6", "x5", "x4", "x3", "x2", "x1", "x0"
  ]


let CIA_fp = RFull("CIA")
let NIA_fp = RFull("NIA")

function initial_analysis (instr:ast) -> (regfps,regfps,regfps,niafps,diafp,instruction_kind) = {
  iR = [| |] : regfps;
  oR = [| |] : regfps;
  aR = [| |] : regfps;
  ik = IK_simple() : instruction_kind;
  Nias = [| NIAFP_successor() |] : niafps;
  Dia = DIAFP_none() : diafp;

  match instr {
     EBREAK() => (),
     UTYPE(imm, rd, op) => {
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
     },
     RISCV_JAL(imm, rd) => {
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
            let offset : bits(64) = EXTS(imm) in
            Nias = [| NIAFP_concrete_address (PC + offset) |];
            ik = IK_branch();
     },
     RISCV_JALR(imm, rs, rd) => {
            if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
            let offset : bits(64) = EXTS(imm) in
            Nias = [| NIAFP_indirect_address() |];
            ik = IK_branch();
     },
     BTYPE(imm, rs2, rs1, op) => {
            if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
            ik = IK_branch();
            let offset : bits(64) = EXTS(imm) in
            Nias = [| NIAFP_concrete_address(PC + offset), NIAFP_successor() |];
      },
      ITYPE(imm, rs, rd, op) => {
            if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      SHIFTIOP(imm, rs, rd, op) => {
             if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      RTYPE(rs2, rs1, rd, op) => {
             if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
             if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      CSR(csr, rs1, rd, is_imm, op) => {
               let isWrite : bool = match op {
                   CSRRW  => true,
                   _      => if is_imm then unsigned(rs1) != 0 else unsigned(rs1) != 0
               };
               iR = RFull(csr_name(csr)) :: iR;
               if ~(is_imm) then {
                  iR = RFull(GPRstr[rs1]) :: iR;
               };
               if isWrite then {
                  oR = RFull(csr_name(csr)) :: oR;
               };
               oR = RFull(GPRstr[rd]) :: oR;
      },
      LOAD(imm, rs, rd, unsign, width, aq, rl) => { /* XXX "unsigned" causes name conflict in lem shallow embedding... */
             if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
             aR = iR;
             ik =
               match (aq, rl) {
                 (false, false) => IK_mem_read (Read_plain),
                 (true,  false) => IK_mem_read (Read_RISCV_acquire),
                 (true,  true)  => IK_mem_read (Read_RISCV_strong_acquire),

                 _  => internal_error("LOAD type not implemented in initial_analysis")
               }
      },
      STORE(imm, rs2, rs1, width, aq, rl) => {
             if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
             if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
             if (rs1 == 0) then () else aR = RFull(GPRstr[rs1]) :: aR;
             ik =
               match (aq, rl) {
                 (false, false) => IK_mem_write (Write_plain),
                 (false, true)  => IK_mem_write (Write_RISCV_release),
                 (true,  true)  => IK_mem_write (Write_RISCV_strong_release),

                 _ => internal_error("STORE type not implemented in initial_analysis")
               }
      },
      ADDIW(imm, rs, rd) => {
             if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      SHIFTW(imm, rs, rd, op) => {
             if (rs == 0) then () else iR = RFull(GPRstr[rs]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      RTYPEW(rs2, rs1, rd, op) => {
             if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
             if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
      },
      FENCE(pred, succ) => {
             ik =
               match (pred, succ) {
                 (_ : bits(2) @ 0b11, _ : bits(2) @ 0b11) => IK_barrier (Barrier_RISCV_rw_rw),
                 (_ : bits(2) @ 0b10, _ : bits(2) @ 0b11) => IK_barrier (Barrier_RISCV_r_rw),
                 (_ : bits(2) @ 0b10, _ : bits(2) @ 0b10) => IK_barrier (Barrier_RISCV_r_r),
                 (_ : bits(2) @ 0b11, _ : bits(2) @ 0b01) => IK_barrier (Barrier_RISCV_rw_w),
                 (_ : bits(2) @ 0b01, _ : bits(2) @ 0b01) => IK_barrier (Barrier_RISCV_w_w),
                 (_ : bits(2) @ 0b01, _ : bits(2) @ 0b11) => IK_barrier (Barrier_RISCV_w_rw),
                 (_ : bits(2) @ 0b11, _ : bits(2) @ 0b10) => IK_barrier (Barrier_RISCV_rw_r),
                 (_ : bits(2) @ 0b10, _ : bits(2) @ 0b01) => IK_barrier (Barrier_RISCV_r_w),
                 (_ : bits(2) @ 0b01, _ : bits(2) @ 0b10) => IK_barrier (Barrier_RISCV_w_r),


                 (_ : bits(2) @ 0b00, _ : bits(2) @ 0b00) => IK_simple (),

                 _ => internal_error("barrier type not implemented in initial_analysis")
  //               case (FM_NORMAL, _, _) -> exit "not implemented"

  //               case (FM_TSO, 0b0011, 0b0011) -> IK_barrier (Barrier_RISCV_tso)
  //               case (FM_TSO, _, _) -> exit "not implemented"
               };
      },
     FENCEI() => {
              ik = IK_barrier (Barrier_RISCV_i);
     },
     LOADRES(aq, rl, rs1, width, rd) => {
            if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
            aR = iR;
            ik = match (aq, rl) {
              (false, false) => IK_mem_read (Read_RISCV_reserved),
              (true,  false) => IK_mem_read (Read_RISCV_reserved_acquire),
              (true,  true)  => IK_mem_read (Read_RISCV_reserved_strong_acquire),
              (false, true)  => internal_error("LOADRES type not implemented in initial_analysis")
            };
     },
     STORECON(aq, rl, rs2, rs1, width, rd) => {
            if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
            if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
            if (rs1 == 0) then () else aR = RFull(GPRstr[rs1]) :: aR;
            if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
             ik = match (aq, rl) {
               (false, false) => IK_mem_write (Write_RISCV_conditional),
               (false, true)  => IK_mem_write (Write_RISCV_conditional_release),
               (true,  true)  => IK_mem_write (Write_RISCV_conditional_strong_release),

               (true,  false) => internal_error("STORECON type not implemented in initial_analysis")
             };
      },
      AMO(op, aq, rl, rs2, rs1, width, rd) => {
             if (rs2 == 0) then () else iR = RFull(GPRstr[rs2]) :: iR;
             if (rs1 == 0) then () else iR = RFull(GPRstr[rs1]) :: iR;
             if (rs1 == 0) then () else aR = RFull(GPRstr[rs1]) :: aR;
             if (rd == 0) then () else oR = RFull(GPRstr[rd]) :: oR;
             ik = match (aq, rl) {
               (false, false) => IK_mem_rmw (Read_RISCV_reserved, Write_RISCV_conditional),
               (false, true)  => IK_mem_rmw (Read_RISCV_reserved, Write_RISCV_conditional_release),
               (true,  false) => IK_mem_rmw (Read_RISCV_reserved_acquire,
                                                                       Write_RISCV_conditional),
               (true,  true)  => IK_mem_rmw (Read_RISCV_reserved_acquire,
                                                                       Write_RISCV_conditional_release)
             };
      },
        _ => ()
  };
  (iR,oR,aR,Nias,Dia,ik)
}
