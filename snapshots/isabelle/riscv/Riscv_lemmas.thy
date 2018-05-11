theory Riscv_lemmas
  imports
    Sail.Sail_values_lemmas
    Sail.State_lemmas
    Riscv
begin

abbreviation "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def tlb39_ref_def tselect_ref_def stval_ref_def
  scause_ref_def sepc_ref_def sscratch_ref_def stvec_ref_def satp_ref_def sideleg_ref_def
  sedeleg_ref_def pmpcfg0_ref_def pmpaddr0_ref_def mhartid_ref_def marchid_ref_def mimpid_ref_def
  mvendorid_ref_def minstret_ref_def mtime_ref_def mcycle_ref_def mscratch_ref_def mtval_ref_def
  mepc_ref_def mcause_ref_def mtvec_ref_def medeleg_ref_def mideleg_ref_def mie_ref_def mip_ref_def
  mstatus_ref_def misa_ref_def cur_inst_ref_def cur_privilege_ref_def Xs_ref_def nextPC_ref_def
  PC_ref_def

lemma regval_Mcause[simp]:
  "Mcause_of_regval (regval_of_Mcause v) = Some v"
  by (auto simp: regval_of_Mcause_def)

lemma regval_Medeleg[simp]:
  "Medeleg_of_regval (regval_of_Medeleg v) = Some v"
  by (auto simp: regval_of_Medeleg_def)

lemma regval_Minterrupts[simp]:
  "Minterrupts_of_regval (regval_of_Minterrupts v) = Some v"
  by (auto simp: regval_of_Minterrupts_def)

lemma regval_Misa[simp]:
  "Misa_of_regval (regval_of_Misa v) = Some v"
  by (auto simp: regval_of_Misa_def)

lemma regval_Mstatus[simp]:
  "Mstatus_of_regval (regval_of_Mstatus v) = Some v"
  by (auto simp: regval_of_Mstatus_def)

lemma regval_Mtvec[simp]:
  "Mtvec_of_regval (regval_of_Mtvec v) = Some v"
  by (auto simp: regval_of_Mtvec_def)

lemma regval_Privilege[simp]:
  "Privilege_of_regval (regval_of_Privilege v) = Some v"
  by (auto simp: regval_of_Privilege_def)

lemma regval_Sedeleg[simp]:
  "Sedeleg_of_regval (regval_of_Sedeleg v) = Some v"
  by (auto simp: regval_of_Sedeleg_def)

lemma regval_Sinterrupts[simp]:
  "Sinterrupts_of_regval (regval_of_Sinterrupts v) = Some v"
  by (auto simp: regval_of_Sinterrupts_def)

lemma regval_TLB39_Entry[simp]:
  "TLB39_Entry_of_regval (regval_of_TLB39_Entry v) = Some v"
  by (auto simp: regval_of_TLB39_Entry_def)

lemma regval_vector_64_dec_bit[simp]:
  "vector_64_dec_bit_of_regval (regval_of_vector_64_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_64_dec_bit_def)

lemma vector_of_rv_rv_of_vector[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "vector_of_regval of_rv (regval_of_vector rv_of len is_inc v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  then show ?thesis by (auto simp: vector_of_regval_def regval_of_vector_def)
qed

lemma liftS_read_reg_tlb39[simp]:
  "liftS (read_reg tlb39_ref) = readS (tlb39 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_tlb39[simp]:
  "liftS (write_reg tlb39_ref v) = updateS (regstate_update (tlb39_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_tselect[simp]:
  "liftS (read_reg tselect_ref) = readS (tselect \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_tselect[simp]:
  "liftS (write_reg tselect_ref v) = updateS (regstate_update (tselect_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_stval[simp]:
  "liftS (read_reg stval_ref) = readS (stval \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_stval[simp]:
  "liftS (write_reg stval_ref v) = updateS (regstate_update (stval_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_scause[simp]:
  "liftS (read_reg scause_ref) = readS (scause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_scause[simp]:
  "liftS (write_reg scause_ref v) = updateS (regstate_update (scause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sepc[simp]:
  "liftS (read_reg sepc_ref) = readS (sepc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sepc[simp]:
  "liftS (write_reg sepc_ref v) = updateS (regstate_update (sepc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sscratch[simp]:
  "liftS (read_reg sscratch_ref) = readS (sscratch \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sscratch[simp]:
  "liftS (write_reg sscratch_ref v) = updateS (regstate_update (sscratch_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_stvec[simp]:
  "liftS (read_reg stvec_ref) = readS (stvec \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_stvec[simp]:
  "liftS (write_reg stvec_ref v) = updateS (regstate_update (stvec_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_satp[simp]:
  "liftS (read_reg satp_ref) = readS (satp \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_satp[simp]:
  "liftS (write_reg satp_ref v) = updateS (regstate_update (satp_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sideleg[simp]:
  "liftS (read_reg sideleg_ref) = readS (sideleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sideleg[simp]:
  "liftS (write_reg sideleg_ref v) = updateS (regstate_update (sideleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sedeleg[simp]:
  "liftS (read_reg sedeleg_ref) = readS (sedeleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sedeleg[simp]:
  "liftS (write_reg sedeleg_ref v) = updateS (regstate_update (sedeleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_pmpcfg0[simp]:
  "liftS (read_reg pmpcfg0_ref) = readS (pmpcfg0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_pmpcfg0[simp]:
  "liftS (write_reg pmpcfg0_ref v) = updateS (regstate_update (pmpcfg0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_pmpaddr0[simp]:
  "liftS (read_reg pmpaddr0_ref) = readS (pmpaddr0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_pmpaddr0[simp]:
  "liftS (write_reg pmpaddr0_ref v) = updateS (regstate_update (pmpaddr0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mhartid[simp]:
  "liftS (read_reg mhartid_ref) = readS (mhartid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mhartid[simp]:
  "liftS (write_reg mhartid_ref v) = updateS (regstate_update (mhartid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_marchid[simp]:
  "liftS (read_reg marchid_ref) = readS (marchid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_marchid[simp]:
  "liftS (write_reg marchid_ref v) = updateS (regstate_update (marchid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mimpid[simp]:
  "liftS (read_reg mimpid_ref) = readS (mimpid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mimpid[simp]:
  "liftS (write_reg mimpid_ref v) = updateS (regstate_update (mimpid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mvendorid[simp]:
  "liftS (read_reg mvendorid_ref) = readS (mvendorid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mvendorid[simp]:
  "liftS (write_reg mvendorid_ref v) = updateS (regstate_update (mvendorid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_minstret[simp]:
  "liftS (read_reg minstret_ref) = readS (minstret \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_minstret[simp]:
  "liftS (write_reg minstret_ref v) = updateS (regstate_update (minstret_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtime[simp]:
  "liftS (read_reg mtime_ref) = readS (mtime \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtime[simp]:
  "liftS (write_reg mtime_ref v) = updateS (regstate_update (mtime_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mcycle[simp]:
  "liftS (read_reg mcycle_ref) = readS (mcycle \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mcycle[simp]:
  "liftS (write_reg mcycle_ref v) = updateS (regstate_update (mcycle_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mscratch[simp]:
  "liftS (read_reg mscratch_ref) = readS (mscratch \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mscratch[simp]:
  "liftS (write_reg mscratch_ref v) = updateS (regstate_update (mscratch_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtval[simp]:
  "liftS (read_reg mtval_ref) = readS (mtval \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtval[simp]:
  "liftS (write_reg mtval_ref v) = updateS (regstate_update (mtval_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mepc[simp]:
  "liftS (read_reg mepc_ref) = readS (mepc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mepc[simp]:
  "liftS (write_reg mepc_ref v) = updateS (regstate_update (mepc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mcause[simp]:
  "liftS (read_reg mcause_ref) = readS (mcause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mcause[simp]:
  "liftS (write_reg mcause_ref v) = updateS (regstate_update (mcause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtvec[simp]:
  "liftS (read_reg mtvec_ref) = readS (mtvec \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtvec[simp]:
  "liftS (write_reg mtvec_ref v) = updateS (regstate_update (mtvec_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_medeleg[simp]:
  "liftS (read_reg medeleg_ref) = readS (medeleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_medeleg[simp]:
  "liftS (write_reg medeleg_ref v) = updateS (regstate_update (medeleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mideleg[simp]:
  "liftS (read_reg mideleg_ref) = readS (mideleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mideleg[simp]:
  "liftS (write_reg mideleg_ref v) = updateS (regstate_update (mideleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mie[simp]:
  "liftS (read_reg mie_ref) = readS (mie \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mie[simp]:
  "liftS (write_reg mie_ref v) = updateS (regstate_update (mie_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mip[simp]:
  "liftS (read_reg mip_ref) = readS (mip \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mip[simp]:
  "liftS (write_reg mip_ref v) = updateS (regstate_update (mip_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mstatus[simp]:
  "liftS (read_reg mstatus_ref) = readS (mstatus \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mstatus[simp]:
  "liftS (write_reg mstatus_ref v) = updateS (regstate_update (mstatus_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_misa[simp]:
  "liftS (read_reg misa_ref) = readS (misa \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_misa[simp]:
  "liftS (write_reg misa_ref v) = updateS (regstate_update (misa_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_cur_inst[simp]:
  "liftS (read_reg cur_inst_ref) = readS (cur_inst \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_cur_inst[simp]:
  "liftS (write_reg cur_inst_ref v) = updateS (regstate_update (cur_inst_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_cur_privilege[simp]:
  "liftS (read_reg cur_privilege_ref) = readS (cur_privilege \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_cur_privilege[simp]:
  "liftS (write_reg cur_privilege_ref v) = updateS (regstate_update (cur_privilege_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_Xs[simp]:
  "liftS (read_reg Xs_ref) = readS (Xs \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_Xs[simp]:
  "liftS (write_reg Xs_ref v) = updateS (regstate_update (Xs_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_nextPC[simp]:
  "liftS (read_reg nextPC_ref) = readS (nextPC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_nextPC[simp]:
  "liftS (write_reg nextPC_ref v) = updateS (regstate_update (nextPC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PC[simp]:
  "liftS (read_reg PC_ref) = readS (PC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PC[simp]:
  "liftS (write_reg PC_ref v) = updateS (regstate_update (PC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

end
