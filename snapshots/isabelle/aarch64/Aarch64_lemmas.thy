theory Aarch64_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Aarch64
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def APDAKeyHi_EL1_ref_def APDAKeyLo_EL1_ref_def
  APDBKeyHi_EL1_ref_def APDBKeyLo_EL1_ref_def APGAKeyHi_EL1_ref_def APGAKeyLo_EL1_ref_def
  APIAKeyHi_EL1_ref_def APIAKeyLo_EL1_ref_def APIBKeyHi_EL1_ref_def APIBKeyLo_EL1_ref_def
  CONTEXTIDR_EL1_ref_def CONTEXTIDR_EL2_ref_def CPACR_EL1_ref_def CPTR_EL2_ref_def CPTR_EL3_ref_def
  DBGBCR_EL1_ref_def DBGBVR_EL1_ref_def DBGEN_ref_def DBGOSDLR_ref_def DBGOSLSR_ref_def
  DBGPRCR_ref_def DBGPRCR_EL1_ref_def DBGWCR_EL1_ref_def DBGWVR_EL1_ref_def DLR_ref_def
  DLR_EL0_ref_def DSPSR_ref_def DSPSR_EL0_ref_def EDSCR_ref_def ELR_EL1_ref_def ELR_EL2_ref_def
  ELR_EL3_ref_def ELR_hyp_ref_def ESR_EL1_ref_def ESR_EL2_ref_def ESR_EL3_ref_def
  EventRegister_ref_def FAR_EL1_ref_def FAR_EL2_ref_def FAR_EL3_ref_def FPCR_ref_def FPEXC_ref_def
  FPSCR_ref_def FPSR_ref_def HCR_ref_def HCR2_ref_def HCR_EL2_ref_def HDCR_ref_def HDFAR_ref_def
  HIFAR_ref_def HPFAR_ref_def HPFAR_EL2_ref_def HSCTLR_ref_def HSR_ref_def HVBAR_ref_def
  ID_AA64DFR0_EL1_ref_def LR_mon_ref_def MAIR_EL1_ref_def MAIR_EL2_ref_def MAIR_EL3_ref_def
  MDCR_EL2_ref_def MDCR_EL3_ref_def MDSCR_EL1_ref_def OSDLR_EL1_ref_def OSLSR_EL1_ref_def
  PSTATE_ref_def RC_ref_def RVBAR_EL1_ref_def RVBAR_EL2_ref_def RVBAR_EL3_ref_def SCR_ref_def
  SCR_EL3_ref_def SCTLR_ref_def SCTLR_EL1_ref_def SCTLR_EL2_ref_def SCTLR_EL3_ref_def SDCR_ref_def
  SDER_ref_def SPIDEN_ref_def SPSR_EL1_ref_def SPSR_EL2_ref_def SPSR_EL3_ref_def SPSR_abt_ref_def
  SPSR_fiq_ref_def SPSR_hyp_ref_def SPSR_irq_ref_def SPSR_mon_ref_def SPSR_svc_ref_def
  SPSR_und_ref_def SP_EL0_ref_def SP_EL1_ref_def SP_EL2_ref_def SP_EL3_ref_def SP_mon_ref_def
  TCR_EL1_ref_def TCR_EL2_ref_def TCR_EL3_ref_def TTBCR_ref_def TTBR0_EL1_ref_def TTBR0_EL2_ref_def
  TTBR0_EL3_ref_def TTBR1_EL1_ref_def TTBR1_EL2_ref_def VBAR_ref_def VBAR_EL1_ref_def
  VBAR_EL2_ref_def VBAR_EL3_ref_def VDFSR_ref_def VSESR_EL2_ref_def VTCR_EL2_ref_def
  VTTBR_EL2_ref_def PC_ref_def R_ref_def V_ref_def BranchTaken_ref_def ExclusiveLocal_ref_def
  Memory_ref_def PendingInterrupt_ref_def PendingPhysicalSError_ref_def Sleeping_ref_def
  ThisInstr_ref_def ThisInstrEnc_ref_def currentCond_ref_def unconditional_ref_def

lemma regval_ProcState[simp]:
  "ProcState_of_regval (regval_of_ProcState v) = Some v"
  by (auto simp: regval_of_ProcState_def)

lemma regval___InstrEnc[simp]:
  "InstrEnc_of_regval (regval_of___InstrEnc v) = Some v"
  by (auto simp: regval_of___InstrEnc_def)

lemma regval_bool[simp]:
  "bool_of_regval (regval_of_bool v) = Some v"
  by (auto simp: regval_of_bool_def)

lemma regval_signal[simp]:
  "signal_of_regval (regval_of_signal v) = Some v"
  by (auto simp: regval_of_signal_def)

lemma regval_vector_128_dec_bit[simp]:
  "vector_128_dec_bit_of_regval (regval_of_vector_128_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_128_dec_bit_def)

lemma regval_vector_1_dec_bit[simp]:
  "vector_1_dec_bit_of_regval (regval_of_vector_1_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_1_dec_bit_def)

lemma regval_vector_32_dec_bit[simp]:
  "vector_32_dec_bit_of_regval (regval_of_vector_32_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_32_dec_bit_def)

lemma regval_vector_4_dec_bit[simp]:
  "vector_4_dec_bit_of_regval (regval_of_vector_4_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_4_dec_bit_def)

lemma regval_vector_52_dec_bit[simp]:
  "vector_52_dec_bit_of_regval (regval_of_vector_52_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_52_dec_bit_def)

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

lemma liftS_read_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APDAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APDAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APDBKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDBKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APDBKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APDBKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APDBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APDBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APDBKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APGAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APGAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APGAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APGAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APGAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APGAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APGAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APGAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APIAKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIAKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIAKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIAKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APIAKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIAKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIAKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIAKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyHi_EL1_ref\<rbrakk>\<^sub>S = readS (APIBKeyHi_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIBKeyHi_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyHi_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIBKeyHi_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>read_reg APIBKeyLo_EL1_ref\<rbrakk>\<^sub>S = readS (APIBKeyLo_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_APIBKeyLo_EL1[liftState_simp]:
  "\<lbrakk>write_reg APIBKeyLo_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (APIBKeyLo_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL1_ref\<rbrakk>\<^sub>S = readS (CONTEXTIDR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CONTEXTIDR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CONTEXTIDR_EL2_ref\<rbrakk>\<^sub>S = readS (CONTEXTIDR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CONTEXTIDR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CONTEXTIDR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CONTEXTIDR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>read_reg CPACR_EL1_ref\<rbrakk>\<^sub>S = readS (CPACR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPACR_EL1[liftState_simp]:
  "\<lbrakk>write_reg CPACR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPACR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL2_ref\<rbrakk>\<^sub>S = readS (CPTR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPTR_EL2[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPTR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>read_reg CPTR_EL3_ref\<rbrakk>\<^sub>S = readS (CPTR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CPTR_EL3[liftState_simp]:
  "\<lbrakk>write_reg CPTR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CPTR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGBCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGBVR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGBVR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGBVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGBVR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGBVR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGEN[liftState_simp]:
  "\<lbrakk>read_reg DBGEN_ref\<rbrakk>\<^sub>S = readS (DBGEN \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGEN[liftState_simp]:
  "\<lbrakk>write_reg DBGEN_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGEN_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGOSDLR[liftState_simp]:
  "\<lbrakk>read_reg DBGOSDLR_ref\<rbrakk>\<^sub>S = readS (DBGOSDLR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGOSDLR[liftState_simp]:
  "\<lbrakk>write_reg DBGOSDLR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGOSDLR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGOSLSR[liftState_simp]:
  "\<lbrakk>read_reg DBGOSLSR_ref\<rbrakk>\<^sub>S = readS (DBGOSLSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGOSLSR[liftState_simp]:
  "\<lbrakk>write_reg DBGOSLSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGOSLSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGPRCR[liftState_simp]:
  "\<lbrakk>read_reg DBGPRCR_ref\<rbrakk>\<^sub>S = readS (DBGPRCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGPRCR[liftState_simp]:
  "\<lbrakk>write_reg DBGPRCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGPRCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGPRCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGPRCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGPRCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGPRCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGPRCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWCR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGWCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>read_reg DBGWVR_EL1_ref\<rbrakk>\<^sub>S = readS (DBGWVR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DBGWVR_EL1[liftState_simp]:
  "\<lbrakk>write_reg DBGWVR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DBGWVR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DLR[liftState_simp]:
  "\<lbrakk>read_reg DLR_ref\<rbrakk>\<^sub>S = readS (DLR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DLR[liftState_simp]:
  "\<lbrakk>write_reg DLR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DLR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DLR_EL0_ref\<rbrakk>\<^sub>S = readS (DLR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DLR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DLR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DLR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DSPSR[liftState_simp]:
  "\<lbrakk>read_reg DSPSR_ref\<rbrakk>\<^sub>S = readS (DSPSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DSPSR[liftState_simp]:
  "\<lbrakk>write_reg DSPSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DSPSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>read_reg DSPSR_EL0_ref\<rbrakk>\<^sub>S = readS (DSPSR_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DSPSR_EL0[liftState_simp]:
  "\<lbrakk>write_reg DSPSR_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DSPSR_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EDSCR[liftState_simp]:
  "\<lbrakk>read_reg EDSCR_ref\<rbrakk>\<^sub>S = readS (EDSCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EDSCR[liftState_simp]:
  "\<lbrakk>write_reg EDSCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EDSCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL1_ref\<rbrakk>\<^sub>S = readS (ELR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL2_ref\<rbrakk>\<^sub>S = readS (ELR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ELR_EL3_ref\<rbrakk>\<^sub>S = readS (ELR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ELR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ELR_hyp[liftState_simp]:
  "\<lbrakk>read_reg ELR_hyp_ref\<rbrakk>\<^sub>S = readS (ELR_hyp \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ELR_hyp[liftState_simp]:
  "\<lbrakk>write_reg ELR_hyp_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ELR_hyp_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL1_ref\<rbrakk>\<^sub>S = readS (ESR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL1[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL2_ref\<rbrakk>\<^sub>S = readS (ESR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>read_reg ESR_EL3_ref\<rbrakk>\<^sub>S = readS (ESR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ESR_EL3[liftState_simp]:
  "\<lbrakk>write_reg ESR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ESR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EventRegister[liftState_simp]:
  "\<lbrakk>read_reg EventRegister_ref\<rbrakk>\<^sub>S = readS (EventRegister \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EventRegister[liftState_simp]:
  "\<lbrakk>write_reg EventRegister_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EventRegister_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL1_ref\<rbrakk>\<^sub>S = readS (FAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL2_ref\<rbrakk>\<^sub>S = readS (FAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg FAR_EL3_ref\<rbrakk>\<^sub>S = readS (FAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg FAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPCR[liftState_simp]:
  "\<lbrakk>read_reg FPCR_ref\<rbrakk>\<^sub>S = readS (FPCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPCR[liftState_simp]:
  "\<lbrakk>write_reg FPCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPEXC[liftState_simp]:
  "\<lbrakk>read_reg FPEXC_ref\<rbrakk>\<^sub>S = readS (FPEXC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPEXC[liftState_simp]:
  "\<lbrakk>write_reg FPEXC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPEXC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPSCR[liftState_simp]:
  "\<lbrakk>read_reg FPSCR_ref\<rbrakk>\<^sub>S = readS (FPSCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPSCR[liftState_simp]:
  "\<lbrakk>write_reg FPSCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPSCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_FPSR[liftState_simp]:
  "\<lbrakk>read_reg FPSR_ref\<rbrakk>\<^sub>S = readS (FPSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_FPSR[liftState_simp]:
  "\<lbrakk>write_reg FPSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (FPSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HCR[liftState_simp]:
  "\<lbrakk>read_reg HCR_ref\<rbrakk>\<^sub>S = readS (HCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HCR[liftState_simp]:
  "\<lbrakk>write_reg HCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HCR2[liftState_simp]:
  "\<lbrakk>read_reg HCR2_ref\<rbrakk>\<^sub>S = readS (HCR2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HCR2[liftState_simp]:
  "\<lbrakk>write_reg HCR2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HCR2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HCR_EL2_ref\<rbrakk>\<^sub>S = readS (HCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HDCR[liftState_simp]:
  "\<lbrakk>read_reg HDCR_ref\<rbrakk>\<^sub>S = readS (HDCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HDCR[liftState_simp]:
  "\<lbrakk>write_reg HDCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HDCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HDFAR[liftState_simp]:
  "\<lbrakk>read_reg HDFAR_ref\<rbrakk>\<^sub>S = readS (HDFAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HDFAR[liftState_simp]:
  "\<lbrakk>write_reg HDFAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HDFAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HIFAR[liftState_simp]:
  "\<lbrakk>read_reg HIFAR_ref\<rbrakk>\<^sub>S = readS (HIFAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HIFAR[liftState_simp]:
  "\<lbrakk>write_reg HIFAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HIFAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HPFAR[liftState_simp]:
  "\<lbrakk>read_reg HPFAR_ref\<rbrakk>\<^sub>S = readS (HPFAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HPFAR[liftState_simp]:
  "\<lbrakk>write_reg HPFAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HPFAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg HPFAR_EL2_ref\<rbrakk>\<^sub>S = readS (HPFAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HPFAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg HPFAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HPFAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HSCTLR[liftState_simp]:
  "\<lbrakk>read_reg HSCTLR_ref\<rbrakk>\<^sub>S = readS (HSCTLR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HSCTLR[liftState_simp]:
  "\<lbrakk>write_reg HSCTLR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HSCTLR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HSR[liftState_simp]:
  "\<lbrakk>read_reg HSR_ref\<rbrakk>\<^sub>S = readS (HSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HSR[liftState_simp]:
  "\<lbrakk>write_reg HSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HVBAR[liftState_simp]:
  "\<lbrakk>read_reg HVBAR_ref\<rbrakk>\<^sub>S = readS (HVBAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HVBAR[liftState_simp]:
  "\<lbrakk>write_reg HVBAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HVBAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg ID_AA64DFR0_EL1_ref\<rbrakk>\<^sub>S = readS (ID_AA64DFR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ID_AA64DFR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg ID_AA64DFR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ID_AA64DFR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LR_mon[liftState_simp]:
  "\<lbrakk>read_reg LR_mon_ref\<rbrakk>\<^sub>S = readS (LR_mon \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LR_mon[liftState_simp]:
  "\<lbrakk>write_reg LR_mon_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LR_mon_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL1_ref\<rbrakk>\<^sub>S = readS (MAIR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL2_ref\<rbrakk>\<^sub>S = readS (MAIR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MAIR_EL3_ref\<rbrakk>\<^sub>S = readS (MAIR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MAIR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MAIR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MAIR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL2_ref\<rbrakk>\<^sub>S = readS (MDCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg MDCR_EL3_ref\<rbrakk>\<^sub>S = readS (MDCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg MDCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg MDSCR_EL1_ref\<rbrakk>\<^sub>S = readS (MDSCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_MDSCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg MDSCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (MDSCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSDLR_EL1_ref\<rbrakk>\<^sub>S = readS (OSDLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSDLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSDLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSDLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg OSLSR_EL1_ref\<rbrakk>\<^sub>S = readS (OSLSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_OSLSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg OSLSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (OSLSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PSTATE[liftState_simp]:
  "\<lbrakk>read_reg PSTATE_ref\<rbrakk>\<^sub>S = readS (PSTATE \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PSTATE[liftState_simp]:
  "\<lbrakk>write_reg PSTATE_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PSTATE_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RC[liftState_simp]:
  "\<lbrakk>read_reg RC_ref\<rbrakk>\<^sub>S = readS (RC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RC[liftState_simp]:
  "\<lbrakk>write_reg RC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL1_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL2_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg RVBAR_EL3_ref\<rbrakk>\<^sub>S = readS (RVBAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_RVBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg RVBAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (RVBAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCR[liftState_simp]:
  "\<lbrakk>read_reg SCR_ref\<rbrakk>\<^sub>S = readS (SCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCR[liftState_simp]:
  "\<lbrakk>write_reg SCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCR_EL3_ref\<rbrakk>\<^sub>S = readS (SCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_ref\<rbrakk>\<^sub>S = readS (SCTLR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL1_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL2_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SCTLR_EL3_ref\<rbrakk>\<^sub>S = readS (SCTLR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SCTLR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SCTLR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SCTLR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SDCR[liftState_simp]:
  "\<lbrakk>read_reg SDCR_ref\<rbrakk>\<^sub>S = readS (SDCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SDCR[liftState_simp]:
  "\<lbrakk>write_reg SDCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SDCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SDER[liftState_simp]:
  "\<lbrakk>read_reg SDER_ref\<rbrakk>\<^sub>S = readS (SDER \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SDER[liftState_simp]:
  "\<lbrakk>write_reg SDER_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SDER_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>read_reg SPIDEN_ref\<rbrakk>\<^sub>S = readS (SPIDEN \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPIDEN[liftState_simp]:
  "\<lbrakk>write_reg SPIDEN_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPIDEN_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL1_ref\<rbrakk>\<^sub>S = readS (SPSR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL1[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL2_ref\<rbrakk>\<^sub>S = readS (SPSR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL2[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>read_reg SPSR_EL3_ref\<rbrakk>\<^sub>S = readS (SPSR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_EL3[liftState_simp]:
  "\<lbrakk>write_reg SPSR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>read_reg SPSR_abt_ref\<rbrakk>\<^sub>S = readS (SPSR_abt \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_abt[liftState_simp]:
  "\<lbrakk>write_reg SPSR_abt_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_abt_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_fiq_ref\<rbrakk>\<^sub>S = readS (SPSR_fiq \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_fiq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_fiq_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_fiq_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_hyp[liftState_simp]:
  "\<lbrakk>read_reg SPSR_hyp_ref\<rbrakk>\<^sub>S = readS (SPSR_hyp \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_hyp[liftState_simp]:
  "\<lbrakk>write_reg SPSR_hyp_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_hyp_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>read_reg SPSR_irq_ref\<rbrakk>\<^sub>S = readS (SPSR_irq \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_irq[liftState_simp]:
  "\<lbrakk>write_reg SPSR_irq_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_irq_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_mon[liftState_simp]:
  "\<lbrakk>read_reg SPSR_mon_ref\<rbrakk>\<^sub>S = readS (SPSR_mon \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_mon[liftState_simp]:
  "\<lbrakk>write_reg SPSR_mon_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_mon_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_svc[liftState_simp]:
  "\<lbrakk>read_reg SPSR_svc_ref\<rbrakk>\<^sub>S = readS (SPSR_svc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_svc[liftState_simp]:
  "\<lbrakk>write_reg SPSR_svc_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_svc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>read_reg SPSR_und_ref\<rbrakk>\<^sub>S = readS (SPSR_und \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SPSR_und[liftState_simp]:
  "\<lbrakk>write_reg SPSR_und_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SPSR_und_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>read_reg SP_EL0_ref\<rbrakk>\<^sub>S = readS (SP_EL0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL0[liftState_simp]:
  "\<lbrakk>write_reg SP_EL0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>read_reg SP_EL1_ref\<rbrakk>\<^sub>S = readS (SP_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL1[liftState_simp]:
  "\<lbrakk>write_reg SP_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>read_reg SP_EL2_ref\<rbrakk>\<^sub>S = readS (SP_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL2[liftState_simp]:
  "\<lbrakk>write_reg SP_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>read_reg SP_EL3_ref\<rbrakk>\<^sub>S = readS (SP_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_EL3[liftState_simp]:
  "\<lbrakk>write_reg SP_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_SP_mon[liftState_simp]:
  "\<lbrakk>read_reg SP_mon_ref\<rbrakk>\<^sub>S = readS (SP_mon \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_SP_mon[liftState_simp]:
  "\<lbrakk>write_reg SP_mon_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (SP_mon_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL1_ref\<rbrakk>\<^sub>S = readS (TCR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL1[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL2_ref\<rbrakk>\<^sub>S = readS (TCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>read_reg TCR_EL3_ref\<rbrakk>\<^sub>S = readS (TCR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TCR_EL3[liftState_simp]:
  "\<lbrakk>write_reg TCR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TCR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBCR[liftState_simp]:
  "\<lbrakk>read_reg TTBCR_ref\<rbrakk>\<^sub>S = readS (TTBCR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBCR[liftState_simp]:
  "\<lbrakk>write_reg TTBCR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBCR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL1_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL2_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>read_reg TTBR0_EL3_ref\<rbrakk>\<^sub>S = readS (TTBR0_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR0_EL3[liftState_simp]:
  "\<lbrakk>write_reg TTBR0_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR0_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL1_ref\<rbrakk>\<^sub>S = readS (TTBR1_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR1_EL1[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR1_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>read_reg TTBR1_EL2_ref\<rbrakk>\<^sub>S = readS (TTBR1_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TTBR1_EL2[liftState_simp]:
  "\<lbrakk>write_reg TTBR1_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TTBR1_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR[liftState_simp]:
  "\<lbrakk>read_reg VBAR_ref\<rbrakk>\<^sub>S = readS (VBAR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR[liftState_simp]:
  "\<lbrakk>write_reg VBAR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL1_ref\<rbrakk>\<^sub>S = readS (VBAR_EL1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL1[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL2_ref\<rbrakk>\<^sub>S = readS (VBAR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>read_reg VBAR_EL3_ref\<rbrakk>\<^sub>S = readS (VBAR_EL3 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VBAR_EL3[liftState_simp]:
  "\<lbrakk>write_reg VBAR_EL3_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VBAR_EL3_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VDFSR[liftState_simp]:
  "\<lbrakk>read_reg VDFSR_ref\<rbrakk>\<^sub>S = readS (VDFSR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VDFSR[liftState_simp]:
  "\<lbrakk>write_reg VDFSR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VDFSR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VSESR_EL2_ref\<rbrakk>\<^sub>S = readS (VSESR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VSESR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VSESR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VSESR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTCR_EL2_ref\<rbrakk>\<^sub>S = readS (VTCR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VTCR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTCR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VTCR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>read_reg VTTBR_EL2_ref\<rbrakk>\<^sub>S = readS (VTTBR_EL2 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_VTTBR_EL2[liftState_simp]:
  "\<lbrakk>write_reg VTTBR_EL2_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (VTTBR_EL2_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PC[liftState_simp]:
  "\<lbrakk>read_reg PC_ref\<rbrakk>\<^sub>S = readS (PC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PC[liftState_simp]:
  "\<lbrakk>write_reg PC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_R[liftState_simp]:
  "\<lbrakk>read_reg R_ref\<rbrakk>\<^sub>S = readS (R \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_R[liftState_simp]:
  "\<lbrakk>write_reg R_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (R_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_V[liftState_simp]:
  "\<lbrakk>read_reg V_ref\<rbrakk>\<^sub>S = readS (V \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_V[liftState_simp]:
  "\<lbrakk>write_reg V_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (V_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>read_reg BranchTaken_ref\<rbrakk>\<^sub>S = readS (BranchTaken \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_BranchTaken[liftState_simp]:
  "\<lbrakk>write_reg BranchTaken_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (BranchTaken_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ExclusiveLocal[liftState_simp]:
  "\<lbrakk>read_reg ExclusiveLocal_ref\<rbrakk>\<^sub>S = readS (ExclusiveLocal \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ExclusiveLocal[liftState_simp]:
  "\<lbrakk>write_reg ExclusiveLocal_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ExclusiveLocal_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_Memory[liftState_simp]:
  "\<lbrakk>read_reg Memory_ref\<rbrakk>\<^sub>S = readS (Memory \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_Memory[liftState_simp]:
  "\<lbrakk>write_reg Memory_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (Memory_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PendingInterrupt[liftState_simp]:
  "\<lbrakk>read_reg PendingInterrupt_ref\<rbrakk>\<^sub>S = readS (PendingInterrupt \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PendingInterrupt[liftState_simp]:
  "\<lbrakk>write_reg PendingInterrupt_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PendingInterrupt_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PendingPhysicalSError[liftState_simp]:
  "\<lbrakk>read_reg PendingPhysicalSError_ref\<rbrakk>\<^sub>S = readS (PendingPhysicalSError \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PendingPhysicalSError[liftState_simp]:
  "\<lbrakk>write_reg PendingPhysicalSError_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PendingPhysicalSError_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_Sleeping[liftState_simp]:
  "\<lbrakk>read_reg Sleeping_ref\<rbrakk>\<^sub>S = readS (Sleeping \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_Sleeping[liftState_simp]:
  "\<lbrakk>write_reg Sleeping_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (Sleeping_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>read_reg ThisInstr_ref\<rbrakk>\<^sub>S = readS (ThisInstr \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ThisInstr[liftState_simp]:
  "\<lbrakk>write_reg ThisInstr_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ThisInstr_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>read_reg ThisInstrEnc_ref\<rbrakk>\<^sub>S = readS (ThisInstrEnc \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_ThisInstrEnc[liftState_simp]:
  "\<lbrakk>write_reg ThisInstrEnc_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (ThisInstrEnc_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_currentCond[liftState_simp]:
  "\<lbrakk>read_reg currentCond_ref\<rbrakk>\<^sub>S = readS (currentCond \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_currentCond[liftState_simp]:
  "\<lbrakk>write_reg currentCond_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (currentCond_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_unconditional[liftState_simp]:
  "\<lbrakk>read_reg unconditional_ref\<rbrakk>\<^sub>S = readS (unconditional \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_unconditional[liftState_simp]:
  "\<lbrakk>write_reg unconditional_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (unconditional_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

end
