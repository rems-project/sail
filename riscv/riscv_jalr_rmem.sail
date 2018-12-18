/* The definition for the memory model. */

function clause execute (RISCV_JALR(imm, rs1, rd)) = {
  /* FIXME: this does not check for a misaligned target address. See riscv_jalr_seq.sail. */
  /* write rd before anything else to prevent unintended strength */
  X(rd) = nextPC; /* compatible with JALR, C.JR and C.JALR */
  let newPC : xlenbits = X(rs1) + EXTS(imm);
  nextPC = newPC[63..1] @ 0b0;
  true
}
