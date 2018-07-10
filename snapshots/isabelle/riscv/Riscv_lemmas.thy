theory Riscv_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Riscv
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def tlb39_ref_def htif_exit_code_ref_def
  htif_done_ref_def htif_tohost_ref_def mtimecmp_ref_def tselect_ref_def stval_ref_def
  scause_ref_def sepc_ref_def sscratch_ref_def stvec_ref_def satp_ref_def sideleg_ref_def
  sedeleg_ref_def pmpcfg0_ref_def pmpaddr0_ref_def mhartid_ref_def marchid_ref_def mimpid_ref_def
  mvendorid_ref_def minstret_written_ref_def minstret_ref_def mtime_ref_def mcycle_ref_def
  scounteren_ref_def mcounteren_ref_def mscratch_ref_def mtval_ref_def mepc_ref_def mcause_ref_def
  mtvec_ref_def medeleg_ref_def mideleg_ref_def mie_ref_def mip_ref_def mstatus_ref_def misa_ref_def
  cur_inst_ref_def cur_privilege_ref_def x31_ref_def x30_ref_def x29_ref_def x28_ref_def x27_ref_def
  x26_ref_def x25_ref_def x24_ref_def x23_ref_def x22_ref_def x21_ref_def x20_ref_def x19_ref_def
  x18_ref_def x17_ref_def x16_ref_def x15_ref_def x14_ref_def x13_ref_def x12_ref_def x11_ref_def
  x10_ref_def x9_ref_def x8_ref_def x7_ref_def x6_ref_def x5_ref_def x4_ref_def x3_ref_def
  x2_ref_def x1_ref_def Xs_ref_def nextPC_ref_def PC_ref_def

lemma regval_Counteren[simp]:
  "Counteren_of_regval (regval_of_Counteren v) = Some v"
  by (auto simp: regval_of_Counteren_def)

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

lemma regval_bool[simp]:
  "bool_of_regval (regval_of_bool v) = Some v"
  by (auto simp: regval_of_bool_def)

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

lemma option_of_rv_rv_of_option[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "option_of_regval of_rv (regval_of_option rv_of v) = Some v"
  using assms by (cases v) (auto simp: option_of_regval_def regval_of_option_def)

lemma list_of_rv_rv_of_list[simp]:
  assumes "\<And>v. of_rv (rv_of v) = Some v"
  shows "list_of_regval of_rv (regval_of_list rv_of v) = Some v"
proof -
  from assms have "of_rv \<circ> rv_of = Some" by auto
  with assms show ?thesis by (induction v) (auto simp: list_of_regval_def regval_of_list_def)
qed

lemma liftS_read_reg_tlb39[liftState_simp]:
  "\<lbrakk>read_reg tlb39_ref\<rbrakk>\<^sub>S = readS (tlb39 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_tlb39[liftState_simp]:
  "\<lbrakk>write_reg tlb39_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (tlb39_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_htif_exit_code[liftState_simp]:
  "\<lbrakk>read_reg htif_exit_code_ref\<rbrakk>\<^sub>S = readS (htif_exit_code \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_htif_exit_code[liftState_simp]:
  "\<lbrakk>write_reg htif_exit_code_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (htif_exit_code_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_htif_done[liftState_simp]:
  "\<lbrakk>read_reg htif_done_ref\<rbrakk>\<^sub>S = readS (htif_done \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_htif_done[liftState_simp]:
  "\<lbrakk>write_reg htif_done_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (htif_done_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_htif_tohost[liftState_simp]:
  "\<lbrakk>read_reg htif_tohost_ref\<rbrakk>\<^sub>S = readS (htif_tohost \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_htif_tohost[liftState_simp]:
  "\<lbrakk>write_reg htif_tohost_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (htif_tohost_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtimecmp[liftState_simp]:
  "\<lbrakk>read_reg mtimecmp_ref\<rbrakk>\<^sub>S = readS (mtimecmp \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtimecmp[liftState_simp]:
  "\<lbrakk>write_reg mtimecmp_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mtimecmp_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_tselect[liftState_simp]:
  "\<lbrakk>read_reg tselect_ref\<rbrakk>\<^sub>S = readS (tselect \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_tselect[liftState_simp]:
  "\<lbrakk>write_reg tselect_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (tselect_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_stval[liftState_simp]:
  "\<lbrakk>read_reg stval_ref\<rbrakk>\<^sub>S = readS (stval \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_stval[liftState_simp]:
  "\<lbrakk>write_reg stval_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (stval_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_scause[liftState_simp]:
  "\<lbrakk>read_reg scause_ref\<rbrakk>\<^sub>S = readS (scause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_scause[liftState_simp]:
  "\<lbrakk>write_reg scause_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (scause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sepc[liftState_simp]:
  "\<lbrakk>read_reg sepc_ref\<rbrakk>\<^sub>S = readS (sepc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sepc[liftState_simp]:
  "\<lbrakk>write_reg sepc_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (sepc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sscratch[liftState_simp]:
  "\<lbrakk>read_reg sscratch_ref\<rbrakk>\<^sub>S = readS (sscratch \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sscratch[liftState_simp]:
  "\<lbrakk>write_reg sscratch_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (sscratch_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_stvec[liftState_simp]:
  "\<lbrakk>read_reg stvec_ref\<rbrakk>\<^sub>S = readS (stvec \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_stvec[liftState_simp]:
  "\<lbrakk>write_reg stvec_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (stvec_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_satp[liftState_simp]:
  "\<lbrakk>read_reg satp_ref\<rbrakk>\<^sub>S = readS (satp \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_satp[liftState_simp]:
  "\<lbrakk>write_reg satp_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (satp_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sideleg[liftState_simp]:
  "\<lbrakk>read_reg sideleg_ref\<rbrakk>\<^sub>S = readS (sideleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sideleg[liftState_simp]:
  "\<lbrakk>write_reg sideleg_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (sideleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_sedeleg[liftState_simp]:
  "\<lbrakk>read_reg sedeleg_ref\<rbrakk>\<^sub>S = readS (sedeleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_sedeleg[liftState_simp]:
  "\<lbrakk>write_reg sedeleg_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (sedeleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_pmpcfg0[liftState_simp]:
  "\<lbrakk>read_reg pmpcfg0_ref\<rbrakk>\<^sub>S = readS (pmpcfg0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_pmpcfg0[liftState_simp]:
  "\<lbrakk>write_reg pmpcfg0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (pmpcfg0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_pmpaddr0[liftState_simp]:
  "\<lbrakk>read_reg pmpaddr0_ref\<rbrakk>\<^sub>S = readS (pmpaddr0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_pmpaddr0[liftState_simp]:
  "\<lbrakk>write_reg pmpaddr0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (pmpaddr0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mhartid[liftState_simp]:
  "\<lbrakk>read_reg mhartid_ref\<rbrakk>\<^sub>S = readS (mhartid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mhartid[liftState_simp]:
  "\<lbrakk>write_reg mhartid_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mhartid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_marchid[liftState_simp]:
  "\<lbrakk>read_reg marchid_ref\<rbrakk>\<^sub>S = readS (marchid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_marchid[liftState_simp]:
  "\<lbrakk>write_reg marchid_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (marchid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mimpid[liftState_simp]:
  "\<lbrakk>read_reg mimpid_ref\<rbrakk>\<^sub>S = readS (mimpid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mimpid[liftState_simp]:
  "\<lbrakk>write_reg mimpid_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mimpid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mvendorid[liftState_simp]:
  "\<lbrakk>read_reg mvendorid_ref\<rbrakk>\<^sub>S = readS (mvendorid \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mvendorid[liftState_simp]:
  "\<lbrakk>write_reg mvendorid_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mvendorid_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_minstret_written[liftState_simp]:
  "\<lbrakk>read_reg minstret_written_ref\<rbrakk>\<^sub>S = readS (minstret_written \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_minstret_written[liftState_simp]:
  "\<lbrakk>write_reg minstret_written_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (minstret_written_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_minstret[liftState_simp]:
  "\<lbrakk>read_reg minstret_ref\<rbrakk>\<^sub>S = readS (minstret \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_minstret[liftState_simp]:
  "\<lbrakk>write_reg minstret_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (minstret_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtime[liftState_simp]:
  "\<lbrakk>read_reg mtime_ref\<rbrakk>\<^sub>S = readS (mtime \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtime[liftState_simp]:
  "\<lbrakk>write_reg mtime_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mtime_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mcycle[liftState_simp]:
  "\<lbrakk>read_reg mcycle_ref\<rbrakk>\<^sub>S = readS (mcycle \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mcycle[liftState_simp]:
  "\<lbrakk>write_reg mcycle_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mcycle_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_scounteren[liftState_simp]:
  "\<lbrakk>read_reg scounteren_ref\<rbrakk>\<^sub>S = readS (scounteren \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_scounteren[liftState_simp]:
  "\<lbrakk>write_reg scounteren_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (scounteren_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mcounteren[liftState_simp]:
  "\<lbrakk>read_reg mcounteren_ref\<rbrakk>\<^sub>S = readS (mcounteren \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mcounteren[liftState_simp]:
  "\<lbrakk>write_reg mcounteren_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mcounteren_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mscratch[liftState_simp]:
  "\<lbrakk>read_reg mscratch_ref\<rbrakk>\<^sub>S = readS (mscratch \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mscratch[liftState_simp]:
  "\<lbrakk>write_reg mscratch_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mscratch_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtval[liftState_simp]:
  "\<lbrakk>read_reg mtval_ref\<rbrakk>\<^sub>S = readS (mtval \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtval[liftState_simp]:
  "\<lbrakk>write_reg mtval_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mtval_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mepc[liftState_simp]:
  "\<lbrakk>read_reg mepc_ref\<rbrakk>\<^sub>S = readS (mepc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mepc[liftState_simp]:
  "\<lbrakk>write_reg mepc_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mepc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mcause[liftState_simp]:
  "\<lbrakk>read_reg mcause_ref\<rbrakk>\<^sub>S = readS (mcause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mcause[liftState_simp]:
  "\<lbrakk>write_reg mcause_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mcause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mtvec[liftState_simp]:
  "\<lbrakk>read_reg mtvec_ref\<rbrakk>\<^sub>S = readS (mtvec \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mtvec[liftState_simp]:
  "\<lbrakk>write_reg mtvec_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mtvec_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_medeleg[liftState_simp]:
  "\<lbrakk>read_reg medeleg_ref\<rbrakk>\<^sub>S = readS (medeleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_medeleg[liftState_simp]:
  "\<lbrakk>write_reg medeleg_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (medeleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mideleg[liftState_simp]:
  "\<lbrakk>read_reg mideleg_ref\<rbrakk>\<^sub>S = readS (mideleg \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mideleg[liftState_simp]:
  "\<lbrakk>write_reg mideleg_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mideleg_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mie[liftState_simp]:
  "\<lbrakk>read_reg mie_ref\<rbrakk>\<^sub>S = readS (mie \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mie[liftState_simp]:
  "\<lbrakk>write_reg mie_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mie_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mip[liftState_simp]:
  "\<lbrakk>read_reg mip_ref\<rbrakk>\<^sub>S = readS (mip \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mip[liftState_simp]:
  "\<lbrakk>write_reg mip_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mip_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_mstatus[liftState_simp]:
  "\<lbrakk>read_reg mstatus_ref\<rbrakk>\<^sub>S = readS (mstatus \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_mstatus[liftState_simp]:
  "\<lbrakk>write_reg mstatus_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (mstatus_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_misa[liftState_simp]:
  "\<lbrakk>read_reg misa_ref\<rbrakk>\<^sub>S = readS (misa \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_misa[liftState_simp]:
  "\<lbrakk>write_reg misa_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (misa_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_cur_inst[liftState_simp]:
  "\<lbrakk>read_reg cur_inst_ref\<rbrakk>\<^sub>S = readS (cur_inst \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_cur_inst[liftState_simp]:
  "\<lbrakk>write_reg cur_inst_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (cur_inst_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_cur_privilege[liftState_simp]:
  "\<lbrakk>read_reg cur_privilege_ref\<rbrakk>\<^sub>S = readS (cur_privilege \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_cur_privilege[liftState_simp]:
  "\<lbrakk>write_reg cur_privilege_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (cur_privilege_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x31[liftState_simp]:
  "\<lbrakk>read_reg x31_ref\<rbrakk>\<^sub>S = readS (x31 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x31[liftState_simp]:
  "\<lbrakk>write_reg x31_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x31_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x30[liftState_simp]:
  "\<lbrakk>read_reg x30_ref\<rbrakk>\<^sub>S = readS (x30 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x30[liftState_simp]:
  "\<lbrakk>write_reg x30_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x30_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x29[liftState_simp]:
  "\<lbrakk>read_reg x29_ref\<rbrakk>\<^sub>S = readS (x29 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x29[liftState_simp]:
  "\<lbrakk>write_reg x29_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x29_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x28[liftState_simp]:
  "\<lbrakk>read_reg x28_ref\<rbrakk>\<^sub>S = readS (x28 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x28[liftState_simp]:
  "\<lbrakk>write_reg x28_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x28_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x27[liftState_simp]:
  "\<lbrakk>read_reg x27_ref\<rbrakk>\<^sub>S = readS (x27 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x27[liftState_simp]:
  "\<lbrakk>write_reg x27_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x27_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x26[liftState_simp]:
  "\<lbrakk>read_reg x26_ref\<rbrakk>\<^sub>S = readS (x26 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x26[liftState_simp]:
  "\<lbrakk>write_reg x26_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x26_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x25[liftState_simp]:
  "\<lbrakk>read_reg x25_ref\<rbrakk>\<^sub>S = readS (x25 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x25[liftState_simp]:
  "\<lbrakk>write_reg x25_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x25_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x24[liftState_simp]:
  "\<lbrakk>read_reg x24_ref\<rbrakk>\<^sub>S = readS (x24 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x24[liftState_simp]:
  "\<lbrakk>write_reg x24_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x24_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x23[liftState_simp]:
  "\<lbrakk>read_reg x23_ref\<rbrakk>\<^sub>S = readS (x23 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x23[liftState_simp]:
  "\<lbrakk>write_reg x23_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x23_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x22[liftState_simp]:
  "\<lbrakk>read_reg x22_ref\<rbrakk>\<^sub>S = readS (x22 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x22[liftState_simp]:
  "\<lbrakk>write_reg x22_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x22_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x21[liftState_simp]:
  "\<lbrakk>read_reg x21_ref\<rbrakk>\<^sub>S = readS (x21 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x21[liftState_simp]:
  "\<lbrakk>write_reg x21_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x21_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x20[liftState_simp]:
  "\<lbrakk>read_reg x20_ref\<rbrakk>\<^sub>S = readS (x20 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x20[liftState_simp]:
  "\<lbrakk>write_reg x20_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x20_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x19[liftState_simp]:
  "\<lbrakk>read_reg x19_ref\<rbrakk>\<^sub>S = readS (x19 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x19[liftState_simp]:
  "\<lbrakk>write_reg x19_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x19_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x18[liftState_simp]:
  "\<lbrakk>read_reg x18_ref\<rbrakk>\<^sub>S = readS (x18 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x18[liftState_simp]:
  "\<lbrakk>write_reg x18_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x18_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x17[liftState_simp]:
  "\<lbrakk>read_reg x17_ref\<rbrakk>\<^sub>S = readS (x17 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x17[liftState_simp]:
  "\<lbrakk>write_reg x17_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x17_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x16[liftState_simp]:
  "\<lbrakk>read_reg x16_ref\<rbrakk>\<^sub>S = readS (x16 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x16[liftState_simp]:
  "\<lbrakk>write_reg x16_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x16_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x15[liftState_simp]:
  "\<lbrakk>read_reg x15_ref\<rbrakk>\<^sub>S = readS (x15 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x15[liftState_simp]:
  "\<lbrakk>write_reg x15_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x15_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x14[liftState_simp]:
  "\<lbrakk>read_reg x14_ref\<rbrakk>\<^sub>S = readS (x14 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x14[liftState_simp]:
  "\<lbrakk>write_reg x14_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x14_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x13[liftState_simp]:
  "\<lbrakk>read_reg x13_ref\<rbrakk>\<^sub>S = readS (x13 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x13[liftState_simp]:
  "\<lbrakk>write_reg x13_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x13_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x12[liftState_simp]:
  "\<lbrakk>read_reg x12_ref\<rbrakk>\<^sub>S = readS (x12 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x12[liftState_simp]:
  "\<lbrakk>write_reg x12_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x12_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x11[liftState_simp]:
  "\<lbrakk>read_reg x11_ref\<rbrakk>\<^sub>S = readS (x11 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x11[liftState_simp]:
  "\<lbrakk>write_reg x11_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x11_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x10[liftState_simp]:
  "\<lbrakk>read_reg x10_ref\<rbrakk>\<^sub>S = readS (x10 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x10[liftState_simp]:
  "\<lbrakk>write_reg x10_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x10_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x9[liftState_simp]:
  "\<lbrakk>read_reg x9_ref\<rbrakk>\<^sub>S = readS (x9 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x9[liftState_simp]:
  "\<lbrakk>write_reg x9_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x9_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x8[liftState_simp]:
  "\<lbrakk>read_reg x8_ref\<rbrakk>\<^sub>S = readS (x8 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x8[liftState_simp]:
  "\<lbrakk>write_reg x8_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x8_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x7[liftState_simp]:
  "\<lbrakk>read_reg x7_ref\<rbrakk>\<^sub>S = readS (x7 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x7[liftState_simp]:
  "\<lbrakk>write_reg x7_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x7_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x6[liftState_simp]:
  "\<lbrakk>read_reg x6_ref\<rbrakk>\<^sub>S = readS (x6 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x6[liftState_simp]:
  "\<lbrakk>write_reg x6_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x6_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x5[liftState_simp]:
  "\<lbrakk>read_reg x5_ref\<rbrakk>\<^sub>S = readS (x5 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x5[liftState_simp]:
  "\<lbrakk>write_reg x5_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x5_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x4[liftState_simp]:
  "\<lbrakk>read_reg x4_ref\<rbrakk>\<^sub>S = readS (x4 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x4[liftState_simp]:
  "\<lbrakk>write_reg x4_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x4_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x3[liftState_simp]:
  "\<lbrakk>read_reg x3_ref\<rbrakk>\<^sub>S = readS (x3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x3[liftState_simp]:
  "\<lbrakk>write_reg x3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x2[liftState_simp]:
  "\<lbrakk>read_reg x2_ref\<rbrakk>\<^sub>S = readS (x2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x2[liftState_simp]:
  "\<lbrakk>write_reg x2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_x1[liftState_simp]:
  "\<lbrakk>read_reg x1_ref\<rbrakk>\<^sub>S = readS (x1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_x1[liftState_simp]:
  "\<lbrakk>write_reg x1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (x1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_Xs[liftState_simp]:
  "\<lbrakk>read_reg Xs_ref\<rbrakk>\<^sub>S = readS (Xs \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_Xs[liftState_simp]:
  "\<lbrakk>write_reg Xs_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (Xs_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_nextPC[liftState_simp]:
  "\<lbrakk>read_reg nextPC_ref\<rbrakk>\<^sub>S = readS (nextPC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_nextPC[liftState_simp]:
  "\<lbrakk>write_reg nextPC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (nextPC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = readS (PC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

end
