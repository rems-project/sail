theory Cheri_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Cheri
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def instCount_ref_def CapCause_ref_def KDC_ref_def
  KR2C_ref_def KR1C_ref_def CTLSP_ref_def CTLSU_ref_def C31_ref_def C30_ref_def C29_ref_def
  C28_ref_def C27_ref_def C26_ref_def C25_ref_def C24_ref_def C23_ref_def C22_ref_def C21_ref_def
  C20_ref_def C19_ref_def C18_ref_def C17_ref_def C16_ref_def C15_ref_def C14_ref_def C13_ref_def
  C12_ref_def C11_ref_def C10_ref_def C09_ref_def C08_ref_def C07_ref_def C06_ref_def C05_ref_def
  C04_ref_def C03_ref_def C02_ref_def C01_ref_def DDC_ref_def inCCallDelay_ref_def nextPCC_ref_def
  delayedPCC_ref_def PCC_ref_def KCC_ref_def EPCC_ref_def UART_RVALID_ref_def UART_RDATA_ref_def
  UART_WRITTEN_ref_def UART_WDATA_ref_def GPR_ref_def LO_ref_def HI_ref_def delayedPC_ref_def
  inBranchDelay_ref_def branchPending_ref_def CP0Status_ref_def CP0ConfigK0_ref_def
  CP0UserLocal_ref_def CP0HWREna_ref_def CP0Count_ref_def CP0BadVAddr_ref_def CP0LLAddr_ref_def
  CP0LLBit_ref_def CP0ErrorEPC_ref_def CP0EPC_ref_def CP0Cause_ref_def CP0Compare_ref_def
  TLBEntry63_ref_def TLBEntry62_ref_def TLBEntry61_ref_def TLBEntry60_ref_def TLBEntry59_ref_def
  TLBEntry58_ref_def TLBEntry57_ref_def TLBEntry56_ref_def TLBEntry55_ref_def TLBEntry54_ref_def
  TLBEntry53_ref_def TLBEntry52_ref_def TLBEntry51_ref_def TLBEntry50_ref_def TLBEntry49_ref_def
  TLBEntry48_ref_def TLBEntry47_ref_def TLBEntry46_ref_def TLBEntry45_ref_def TLBEntry44_ref_def
  TLBEntry43_ref_def TLBEntry42_ref_def TLBEntry41_ref_def TLBEntry40_ref_def TLBEntry39_ref_def
  TLBEntry38_ref_def TLBEntry37_ref_def TLBEntry36_ref_def TLBEntry35_ref_def TLBEntry34_ref_def
  TLBEntry33_ref_def TLBEntry32_ref_def TLBEntry31_ref_def TLBEntry30_ref_def TLBEntry29_ref_def
  TLBEntry28_ref_def TLBEntry27_ref_def TLBEntry26_ref_def TLBEntry25_ref_def TLBEntry24_ref_def
  TLBEntry23_ref_def TLBEntry22_ref_def TLBEntry21_ref_def TLBEntry20_ref_def TLBEntry19_ref_def
  TLBEntry18_ref_def TLBEntry17_ref_def TLBEntry16_ref_def TLBEntry15_ref_def TLBEntry14_ref_def
  TLBEntry13_ref_def TLBEntry12_ref_def TLBEntry11_ref_def TLBEntry10_ref_def TLBEntry09_ref_def
  TLBEntry08_ref_def TLBEntry07_ref_def TLBEntry06_ref_def TLBEntry05_ref_def TLBEntry04_ref_def
  TLBEntry03_ref_def TLBEntry02_ref_def TLBEntry01_ref_def TLBEntry00_ref_def TLBXContext_ref_def
  TLBEntryHi_ref_def TLBWired_ref_def TLBPageMask_ref_def TLBContext_ref_def TLBEntryLo1_ref_def
  TLBEntryLo0_ref_def TLBRandom_ref_def TLBIndex_ref_def TLBProbe_ref_def nextPC_ref_def PC_ref_def

lemma regval_CapCauseReg[simp]:
  "CapCauseReg_of_regval (regval_of_CapCauseReg v) = Some v"
  by (auto simp: regval_of_CapCauseReg_def)

lemma regval_CauseReg[simp]:
  "CauseReg_of_regval (regval_of_CauseReg v) = Some v"
  by (auto simp: regval_of_CauseReg_def)

lemma regval_ContextReg[simp]:
  "ContextReg_of_regval (regval_of_ContextReg v) = Some v"
  by (auto simp: regval_of_ContextReg_def)

lemma regval_StatusReg[simp]:
  "StatusReg_of_regval (regval_of_StatusReg v) = Some v"
  by (auto simp: regval_of_StatusReg_def)

lemma regval_TLBEntry[simp]:
  "TLBEntry_of_regval (regval_of_TLBEntry v) = Some v"
  by (auto simp: regval_of_TLBEntry_def)

lemma regval_TLBEntryHiReg[simp]:
  "TLBEntryHiReg_of_regval (regval_of_TLBEntryHiReg v) = Some v"
  by (auto simp: regval_of_TLBEntryHiReg_def)

lemma regval_TLBEntryLoReg[simp]:
  "TLBEntryLoReg_of_regval (regval_of_TLBEntryLoReg v) = Some v"
  by (auto simp: regval_of_TLBEntryLoReg_def)

lemma regval_XContextReg[simp]:
  "XContextReg_of_regval (regval_of_XContextReg v) = Some v"
  by (auto simp: regval_of_XContextReg_def)

lemma regval_int[simp]:
  "int_of_regval (regval_of_int v) = Some v"
  by (auto simp: regval_of_int_def)

lemma regval_vector_16_dec_bit[simp]:
  "vector_16_dec_bit_of_regval (regval_of_vector_16_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_16_dec_bit_def)

lemma regval_vector_1_dec_bit[simp]:
  "vector_1_dec_bit_of_regval (regval_of_vector_1_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_1_dec_bit_def)

lemma regval_vector_257_dec_bit[simp]:
  "vector_257_dec_bit_of_regval (regval_of_vector_257_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_257_dec_bit_def)

lemma regval_vector_32_dec_bit[simp]:
  "vector_32_dec_bit_of_regval (regval_of_vector_32_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_32_dec_bit_def)

lemma regval_vector_3_dec_bit[simp]:
  "vector_3_dec_bit_of_regval (regval_of_vector_3_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_3_dec_bit_def)

lemma regval_vector_64_dec_bit[simp]:
  "vector_64_dec_bit_of_regval (regval_of_vector_64_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_64_dec_bit_def)

lemma regval_vector_6_dec_bit[simp]:
  "vector_6_dec_bit_of_regval (regval_of_vector_6_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_6_dec_bit_def)

lemma regval_vector_8_dec_bit[simp]:
  "vector_8_dec_bit_of_regval (regval_of_vector_8_dec_bit v) = Some v"
  by (auto simp: regval_of_vector_8_dec_bit_def)

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

lemma liftS_read_reg_instCount[liftState_simp]:
  "\<lbrakk>read_reg instCount_ref\<rbrakk>\<^sub>S = readS (instCount \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_instCount[liftState_simp]:
  "\<lbrakk>write_reg instCount_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (instCount_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CapCause[liftState_simp]:
  "\<lbrakk>read_reg CapCause_ref\<rbrakk>\<^sub>S = readS (CapCause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CapCause[liftState_simp]:
  "\<lbrakk>write_reg CapCause_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CapCause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_KDC[liftState_simp]:
  "\<lbrakk>read_reg KDC_ref\<rbrakk>\<^sub>S = readS (KDC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_KDC[liftState_simp]:
  "\<lbrakk>write_reg KDC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (KDC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_KR2C[liftState_simp]:
  "\<lbrakk>read_reg KR2C_ref\<rbrakk>\<^sub>S = readS (KR2C \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_KR2C[liftState_simp]:
  "\<lbrakk>write_reg KR2C_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (KR2C_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_KR1C[liftState_simp]:
  "\<lbrakk>read_reg KR1C_ref\<rbrakk>\<^sub>S = readS (KR1C \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_KR1C[liftState_simp]:
  "\<lbrakk>write_reg KR1C_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (KR1C_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CTLSP[liftState_simp]:
  "\<lbrakk>read_reg CTLSP_ref\<rbrakk>\<^sub>S = readS (CTLSP \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CTLSP[liftState_simp]:
  "\<lbrakk>write_reg CTLSP_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CTLSP_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CTLSU[liftState_simp]:
  "\<lbrakk>read_reg CTLSU_ref\<rbrakk>\<^sub>S = readS (CTLSU \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CTLSU[liftState_simp]:
  "\<lbrakk>write_reg CTLSU_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CTLSU_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C31[liftState_simp]:
  "\<lbrakk>read_reg C31_ref\<rbrakk>\<^sub>S = readS (C31 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C31[liftState_simp]:
  "\<lbrakk>write_reg C31_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C31_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C30[liftState_simp]:
  "\<lbrakk>read_reg C30_ref\<rbrakk>\<^sub>S = readS (C30 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C30[liftState_simp]:
  "\<lbrakk>write_reg C30_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C30_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C29[liftState_simp]:
  "\<lbrakk>read_reg C29_ref\<rbrakk>\<^sub>S = readS (C29 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C29[liftState_simp]:
  "\<lbrakk>write_reg C29_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C29_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C28[liftState_simp]:
  "\<lbrakk>read_reg C28_ref\<rbrakk>\<^sub>S = readS (C28 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C28[liftState_simp]:
  "\<lbrakk>write_reg C28_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C28_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C27[liftState_simp]:
  "\<lbrakk>read_reg C27_ref\<rbrakk>\<^sub>S = readS (C27 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C27[liftState_simp]:
  "\<lbrakk>write_reg C27_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C27_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C26[liftState_simp]:
  "\<lbrakk>read_reg C26_ref\<rbrakk>\<^sub>S = readS (C26 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C26[liftState_simp]:
  "\<lbrakk>write_reg C26_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C26_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C25[liftState_simp]:
  "\<lbrakk>read_reg C25_ref\<rbrakk>\<^sub>S = readS (C25 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C25[liftState_simp]:
  "\<lbrakk>write_reg C25_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C25_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C24[liftState_simp]:
  "\<lbrakk>read_reg C24_ref\<rbrakk>\<^sub>S = readS (C24 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C24[liftState_simp]:
  "\<lbrakk>write_reg C24_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C24_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C23[liftState_simp]:
  "\<lbrakk>read_reg C23_ref\<rbrakk>\<^sub>S = readS (C23 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C23[liftState_simp]:
  "\<lbrakk>write_reg C23_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C23_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C22[liftState_simp]:
  "\<lbrakk>read_reg C22_ref\<rbrakk>\<^sub>S = readS (C22 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C22[liftState_simp]:
  "\<lbrakk>write_reg C22_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C22_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C21[liftState_simp]:
  "\<lbrakk>read_reg C21_ref\<rbrakk>\<^sub>S = readS (C21 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C21[liftState_simp]:
  "\<lbrakk>write_reg C21_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C21_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C20[liftState_simp]:
  "\<lbrakk>read_reg C20_ref\<rbrakk>\<^sub>S = readS (C20 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C20[liftState_simp]:
  "\<lbrakk>write_reg C20_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C20_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C19[liftState_simp]:
  "\<lbrakk>read_reg C19_ref\<rbrakk>\<^sub>S = readS (C19 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C19[liftState_simp]:
  "\<lbrakk>write_reg C19_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C19_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C18[liftState_simp]:
  "\<lbrakk>read_reg C18_ref\<rbrakk>\<^sub>S = readS (C18 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C18[liftState_simp]:
  "\<lbrakk>write_reg C18_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C18_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C17[liftState_simp]:
  "\<lbrakk>read_reg C17_ref\<rbrakk>\<^sub>S = readS (C17 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C17[liftState_simp]:
  "\<lbrakk>write_reg C17_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C17_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C16[liftState_simp]:
  "\<lbrakk>read_reg C16_ref\<rbrakk>\<^sub>S = readS (C16 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C16[liftState_simp]:
  "\<lbrakk>write_reg C16_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C16_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C15[liftState_simp]:
  "\<lbrakk>read_reg C15_ref\<rbrakk>\<^sub>S = readS (C15 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C15[liftState_simp]:
  "\<lbrakk>write_reg C15_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C15_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C14[liftState_simp]:
  "\<lbrakk>read_reg C14_ref\<rbrakk>\<^sub>S = readS (C14 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C14[liftState_simp]:
  "\<lbrakk>write_reg C14_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C14_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C13[liftState_simp]:
  "\<lbrakk>read_reg C13_ref\<rbrakk>\<^sub>S = readS (C13 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C13[liftState_simp]:
  "\<lbrakk>write_reg C13_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C13_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C12[liftState_simp]:
  "\<lbrakk>read_reg C12_ref\<rbrakk>\<^sub>S = readS (C12 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C12[liftState_simp]:
  "\<lbrakk>write_reg C12_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C12_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C11[liftState_simp]:
  "\<lbrakk>read_reg C11_ref\<rbrakk>\<^sub>S = readS (C11 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C11[liftState_simp]:
  "\<lbrakk>write_reg C11_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C11_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C10[liftState_simp]:
  "\<lbrakk>read_reg C10_ref\<rbrakk>\<^sub>S = readS (C10 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C10[liftState_simp]:
  "\<lbrakk>write_reg C10_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C10_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C09[liftState_simp]:
  "\<lbrakk>read_reg C09_ref\<rbrakk>\<^sub>S = readS (C09 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C09[liftState_simp]:
  "\<lbrakk>write_reg C09_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C09_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C08[liftState_simp]:
  "\<lbrakk>read_reg C08_ref\<rbrakk>\<^sub>S = readS (C08 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C08[liftState_simp]:
  "\<lbrakk>write_reg C08_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C08_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C07[liftState_simp]:
  "\<lbrakk>read_reg C07_ref\<rbrakk>\<^sub>S = readS (C07 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C07[liftState_simp]:
  "\<lbrakk>write_reg C07_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C07_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C06[liftState_simp]:
  "\<lbrakk>read_reg C06_ref\<rbrakk>\<^sub>S = readS (C06 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C06[liftState_simp]:
  "\<lbrakk>write_reg C06_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C06_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C05[liftState_simp]:
  "\<lbrakk>read_reg C05_ref\<rbrakk>\<^sub>S = readS (C05 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C05[liftState_simp]:
  "\<lbrakk>write_reg C05_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C05_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C04[liftState_simp]:
  "\<lbrakk>read_reg C04_ref\<rbrakk>\<^sub>S = readS (C04 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C04[liftState_simp]:
  "\<lbrakk>write_reg C04_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C04_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C03[liftState_simp]:
  "\<lbrakk>read_reg C03_ref\<rbrakk>\<^sub>S = readS (C03 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C03[liftState_simp]:
  "\<lbrakk>write_reg C03_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C03_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C02[liftState_simp]:
  "\<lbrakk>read_reg C02_ref\<rbrakk>\<^sub>S = readS (C02 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C02[liftState_simp]:
  "\<lbrakk>write_reg C02_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C02_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_C01[liftState_simp]:
  "\<lbrakk>read_reg C01_ref\<rbrakk>\<^sub>S = readS (C01 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_C01[liftState_simp]:
  "\<lbrakk>write_reg C01_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (C01_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_DDC[liftState_simp]:
  "\<lbrakk>read_reg DDC_ref\<rbrakk>\<^sub>S = readS (DDC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_DDC[liftState_simp]:
  "\<lbrakk>write_reg DDC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (DDC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_inCCallDelay[liftState_simp]:
  "\<lbrakk>read_reg inCCallDelay_ref\<rbrakk>\<^sub>S = readS (inCCallDelay \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_inCCallDelay[liftState_simp]:
  "\<lbrakk>write_reg inCCallDelay_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (inCCallDelay_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_nextPCC[liftState_simp]:
  "\<lbrakk>read_reg nextPCC_ref\<rbrakk>\<^sub>S = readS (nextPCC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_nextPCC[liftState_simp]:
  "\<lbrakk>write_reg nextPCC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (nextPCC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_delayedPCC[liftState_simp]:
  "\<lbrakk>read_reg delayedPCC_ref\<rbrakk>\<^sub>S = readS (delayedPCC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_delayedPCC[liftState_simp]:
  "\<lbrakk>write_reg delayedPCC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (delayedPCC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_PCC[liftState_simp]:
  "\<lbrakk>read_reg PCC_ref\<rbrakk>\<^sub>S = readS (PCC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_PCC[liftState_simp]:
  "\<lbrakk>write_reg PCC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (PCC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_KCC[liftState_simp]:
  "\<lbrakk>read_reg KCC_ref\<rbrakk>\<^sub>S = readS (KCC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_KCC[liftState_simp]:
  "\<lbrakk>write_reg KCC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (KCC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_EPCC[liftState_simp]:
  "\<lbrakk>read_reg EPCC_ref\<rbrakk>\<^sub>S = readS (EPCC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_EPCC[liftState_simp]:
  "\<lbrakk>write_reg EPCC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (EPCC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_UART_RVALID[liftState_simp]:
  "\<lbrakk>read_reg UART_RVALID_ref\<rbrakk>\<^sub>S = readS (UART_RVALID \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_UART_RVALID[liftState_simp]:
  "\<lbrakk>write_reg UART_RVALID_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (UART_RVALID_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_UART_RDATA[liftState_simp]:
  "\<lbrakk>read_reg UART_RDATA_ref\<rbrakk>\<^sub>S = readS (UART_RDATA \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_UART_RDATA[liftState_simp]:
  "\<lbrakk>write_reg UART_RDATA_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (UART_RDATA_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_UART_WRITTEN[liftState_simp]:
  "\<lbrakk>read_reg UART_WRITTEN_ref\<rbrakk>\<^sub>S = readS (UART_WRITTEN \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_UART_WRITTEN[liftState_simp]:
  "\<lbrakk>write_reg UART_WRITTEN_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (UART_WRITTEN_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_UART_WDATA[liftState_simp]:
  "\<lbrakk>read_reg UART_WDATA_ref\<rbrakk>\<^sub>S = readS (UART_WDATA \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_UART_WDATA[liftState_simp]:
  "\<lbrakk>write_reg UART_WDATA_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (UART_WDATA_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_GPR[liftState_simp]:
  "\<lbrakk>read_reg GPR_ref\<rbrakk>\<^sub>S = readS (GPR \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_GPR[liftState_simp]:
  "\<lbrakk>write_reg GPR_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (GPR_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_LO[liftState_simp]:
  "\<lbrakk>read_reg LO_ref\<rbrakk>\<^sub>S = readS (LO \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_LO[liftState_simp]:
  "\<lbrakk>write_reg LO_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (LO_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_HI[liftState_simp]:
  "\<lbrakk>read_reg HI_ref\<rbrakk>\<^sub>S = readS (HI \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_HI[liftState_simp]:
  "\<lbrakk>write_reg HI_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (HI_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_delayedPC[liftState_simp]:
  "\<lbrakk>read_reg delayedPC_ref\<rbrakk>\<^sub>S = readS (delayedPC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_delayedPC[liftState_simp]:
  "\<lbrakk>write_reg delayedPC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (delayedPC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_inBranchDelay[liftState_simp]:
  "\<lbrakk>read_reg inBranchDelay_ref\<rbrakk>\<^sub>S = readS (inBranchDelay \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_inBranchDelay[liftState_simp]:
  "\<lbrakk>write_reg inBranchDelay_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (inBranchDelay_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_branchPending[liftState_simp]:
  "\<lbrakk>read_reg branchPending_ref\<rbrakk>\<^sub>S = readS (branchPending \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_branchPending[liftState_simp]:
  "\<lbrakk>write_reg branchPending_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (branchPending_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0Status[liftState_simp]:
  "\<lbrakk>read_reg CP0Status_ref\<rbrakk>\<^sub>S = readS (CP0Status \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0Status[liftState_simp]:
  "\<lbrakk>write_reg CP0Status_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0Status_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0ConfigK0[liftState_simp]:
  "\<lbrakk>read_reg CP0ConfigK0_ref\<rbrakk>\<^sub>S = readS (CP0ConfigK0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0ConfigK0[liftState_simp]:
  "\<lbrakk>write_reg CP0ConfigK0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0ConfigK0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0UserLocal[liftState_simp]:
  "\<lbrakk>read_reg CP0UserLocal_ref\<rbrakk>\<^sub>S = readS (CP0UserLocal \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0UserLocal[liftState_simp]:
  "\<lbrakk>write_reg CP0UserLocal_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0UserLocal_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0HWREna[liftState_simp]:
  "\<lbrakk>read_reg CP0HWREna_ref\<rbrakk>\<^sub>S = readS (CP0HWREna \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0HWREna[liftState_simp]:
  "\<lbrakk>write_reg CP0HWREna_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0HWREna_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0Count[liftState_simp]:
  "\<lbrakk>read_reg CP0Count_ref\<rbrakk>\<^sub>S = readS (CP0Count \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0Count[liftState_simp]:
  "\<lbrakk>write_reg CP0Count_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0Count_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0BadVAddr[liftState_simp]:
  "\<lbrakk>read_reg CP0BadVAddr_ref\<rbrakk>\<^sub>S = readS (CP0BadVAddr \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0BadVAddr[liftState_simp]:
  "\<lbrakk>write_reg CP0BadVAddr_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0BadVAddr_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0LLAddr[liftState_simp]:
  "\<lbrakk>read_reg CP0LLAddr_ref\<rbrakk>\<^sub>S = readS (CP0LLAddr \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0LLAddr[liftState_simp]:
  "\<lbrakk>write_reg CP0LLAddr_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0LLAddr_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0LLBit[liftState_simp]:
  "\<lbrakk>read_reg CP0LLBit_ref\<rbrakk>\<^sub>S = readS (CP0LLBit \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0LLBit[liftState_simp]:
  "\<lbrakk>write_reg CP0LLBit_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0LLBit_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0ErrorEPC[liftState_simp]:
  "\<lbrakk>read_reg CP0ErrorEPC_ref\<rbrakk>\<^sub>S = readS (CP0ErrorEPC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0ErrorEPC[liftState_simp]:
  "\<lbrakk>write_reg CP0ErrorEPC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0ErrorEPC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0EPC[liftState_simp]:
  "\<lbrakk>read_reg CP0EPC_ref\<rbrakk>\<^sub>S = readS (CP0EPC \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0EPC[liftState_simp]:
  "\<lbrakk>write_reg CP0EPC_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0EPC_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0Cause[liftState_simp]:
  "\<lbrakk>read_reg CP0Cause_ref\<rbrakk>\<^sub>S = readS (CP0Cause \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0Cause[liftState_simp]:
  "\<lbrakk>write_reg CP0Cause_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0Cause_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_CP0Compare[liftState_simp]:
  "\<lbrakk>read_reg CP0Compare_ref\<rbrakk>\<^sub>S = readS (CP0Compare \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_CP0Compare[liftState_simp]:
  "\<lbrakk>write_reg CP0Compare_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (CP0Compare_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry63[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry63_ref\<rbrakk>\<^sub>S = readS (TLBEntry63 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry63[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry63_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry63_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry62[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry62_ref\<rbrakk>\<^sub>S = readS (TLBEntry62 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry62[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry62_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry62_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry61[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry61_ref\<rbrakk>\<^sub>S = readS (TLBEntry61 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry61[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry61_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry61_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry60[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry60_ref\<rbrakk>\<^sub>S = readS (TLBEntry60 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry60[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry60_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry60_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry59[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry59_ref\<rbrakk>\<^sub>S = readS (TLBEntry59 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry59[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry59_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry59_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry58[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry58_ref\<rbrakk>\<^sub>S = readS (TLBEntry58 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry58[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry58_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry58_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry57[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry57_ref\<rbrakk>\<^sub>S = readS (TLBEntry57 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry57[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry57_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry57_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry56[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry56_ref\<rbrakk>\<^sub>S = readS (TLBEntry56 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry56[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry56_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry56_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry55[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry55_ref\<rbrakk>\<^sub>S = readS (TLBEntry55 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry55[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry55_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry55_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry54[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry54_ref\<rbrakk>\<^sub>S = readS (TLBEntry54 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry54[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry54_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry54_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry53[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry53_ref\<rbrakk>\<^sub>S = readS (TLBEntry53 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry53[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry53_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry53_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry52[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry52_ref\<rbrakk>\<^sub>S = readS (TLBEntry52 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry52[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry52_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry52_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry51[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry51_ref\<rbrakk>\<^sub>S = readS (TLBEntry51 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry51[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry51_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry51_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry50[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry50_ref\<rbrakk>\<^sub>S = readS (TLBEntry50 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry50[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry50_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry50_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry49[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry49_ref\<rbrakk>\<^sub>S = readS (TLBEntry49 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry49[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry49_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry49_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry48[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry48_ref\<rbrakk>\<^sub>S = readS (TLBEntry48 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry48[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry48_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry48_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry47[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry47_ref\<rbrakk>\<^sub>S = readS (TLBEntry47 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry47[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry47_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry47_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry46[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry46_ref\<rbrakk>\<^sub>S = readS (TLBEntry46 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry46[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry46_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry46_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry45[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry45_ref\<rbrakk>\<^sub>S = readS (TLBEntry45 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry45[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry45_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry45_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry44[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry44_ref\<rbrakk>\<^sub>S = readS (TLBEntry44 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry44[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry44_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry44_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry43[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry43_ref\<rbrakk>\<^sub>S = readS (TLBEntry43 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry43[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry43_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry43_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry42[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry42_ref\<rbrakk>\<^sub>S = readS (TLBEntry42 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry42[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry42_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry42_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry41[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry41_ref\<rbrakk>\<^sub>S = readS (TLBEntry41 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry41[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry41_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry41_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry40[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry40_ref\<rbrakk>\<^sub>S = readS (TLBEntry40 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry40[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry40_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry40_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry39[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry39_ref\<rbrakk>\<^sub>S = readS (TLBEntry39 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry39[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry39_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry39_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry38[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry38_ref\<rbrakk>\<^sub>S = readS (TLBEntry38 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry38[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry38_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry38_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry37[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry37_ref\<rbrakk>\<^sub>S = readS (TLBEntry37 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry37[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry37_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry37_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry36[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry36_ref\<rbrakk>\<^sub>S = readS (TLBEntry36 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry36[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry36_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry36_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry35[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry35_ref\<rbrakk>\<^sub>S = readS (TLBEntry35 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry35[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry35_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry35_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry34[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry34_ref\<rbrakk>\<^sub>S = readS (TLBEntry34 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry34[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry34_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry34_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry33[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry33_ref\<rbrakk>\<^sub>S = readS (TLBEntry33 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry33[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry33_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry33_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry32[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry32_ref\<rbrakk>\<^sub>S = readS (TLBEntry32 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry32[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry32_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry32_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry31[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry31_ref\<rbrakk>\<^sub>S = readS (TLBEntry31 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry31[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry31_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry31_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry30[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry30_ref\<rbrakk>\<^sub>S = readS (TLBEntry30 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry30[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry30_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry30_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry29[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry29_ref\<rbrakk>\<^sub>S = readS (TLBEntry29 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry29[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry29_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry29_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry28[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry28_ref\<rbrakk>\<^sub>S = readS (TLBEntry28 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry28[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry28_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry28_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry27[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry27_ref\<rbrakk>\<^sub>S = readS (TLBEntry27 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry27[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry27_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry27_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry26[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry26_ref\<rbrakk>\<^sub>S = readS (TLBEntry26 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry26[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry26_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry26_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry25[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry25_ref\<rbrakk>\<^sub>S = readS (TLBEntry25 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry25[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry25_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry25_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry24[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry24_ref\<rbrakk>\<^sub>S = readS (TLBEntry24 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry24[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry24_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry24_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry23[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry23_ref\<rbrakk>\<^sub>S = readS (TLBEntry23 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry23[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry23_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry23_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry22[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry22_ref\<rbrakk>\<^sub>S = readS (TLBEntry22 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry22[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry22_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry22_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry21[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry21_ref\<rbrakk>\<^sub>S = readS (TLBEntry21 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry21[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry21_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry21_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry20[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry20_ref\<rbrakk>\<^sub>S = readS (TLBEntry20 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry20[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry20_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry20_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry19[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry19_ref\<rbrakk>\<^sub>S = readS (TLBEntry19 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry19[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry19_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry19_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry18[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry18_ref\<rbrakk>\<^sub>S = readS (TLBEntry18 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry18[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry18_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry18_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry17[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry17_ref\<rbrakk>\<^sub>S = readS (TLBEntry17 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry17[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry17_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry17_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry16[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry16_ref\<rbrakk>\<^sub>S = readS (TLBEntry16 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry16[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry16_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry16_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry15[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry15_ref\<rbrakk>\<^sub>S = readS (TLBEntry15 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry15[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry15_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry15_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry14[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry14_ref\<rbrakk>\<^sub>S = readS (TLBEntry14 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry14[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry14_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry14_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry13[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry13_ref\<rbrakk>\<^sub>S = readS (TLBEntry13 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry13[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry13_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry13_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry12[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry12_ref\<rbrakk>\<^sub>S = readS (TLBEntry12 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry12[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry12_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry12_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry11[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry11_ref\<rbrakk>\<^sub>S = readS (TLBEntry11 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry11[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry11_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry11_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry10[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry10_ref\<rbrakk>\<^sub>S = readS (TLBEntry10 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry10[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry10_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry10_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry09[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry09_ref\<rbrakk>\<^sub>S = readS (TLBEntry09 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry09[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry09_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry09_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry08[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry08_ref\<rbrakk>\<^sub>S = readS (TLBEntry08 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry08[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry08_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry08_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry07[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry07_ref\<rbrakk>\<^sub>S = readS (TLBEntry07 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry07[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry07_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry07_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry06[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry06_ref\<rbrakk>\<^sub>S = readS (TLBEntry06 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry06[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry06_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry06_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry05[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry05_ref\<rbrakk>\<^sub>S = readS (TLBEntry05 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry05[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry05_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry05_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry04[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry04_ref\<rbrakk>\<^sub>S = readS (TLBEntry04 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry04[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry04_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry04_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry03[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry03_ref\<rbrakk>\<^sub>S = readS (TLBEntry03 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry03[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry03_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry03_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry02[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry02_ref\<rbrakk>\<^sub>S = readS (TLBEntry02 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry02[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry02_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry02_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry01[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry01_ref\<rbrakk>\<^sub>S = readS (TLBEntry01 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry01[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry01_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry01_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntry00[liftState_simp]:
  "\<lbrakk>read_reg TLBEntry00_ref\<rbrakk>\<^sub>S = readS (TLBEntry00 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntry00[liftState_simp]:
  "\<lbrakk>write_reg TLBEntry00_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntry00_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBXContext[liftState_simp]:
  "\<lbrakk>read_reg TLBXContext_ref\<rbrakk>\<^sub>S = readS (TLBXContext \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBXContext[liftState_simp]:
  "\<lbrakk>write_reg TLBXContext_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBXContext_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntryHi[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryHi_ref\<rbrakk>\<^sub>S = readS (TLBEntryHi \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntryHi[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryHi_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntryHi_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBWired[liftState_simp]:
  "\<lbrakk>read_reg TLBWired_ref\<rbrakk>\<^sub>S = readS (TLBWired \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBWired[liftState_simp]:
  "\<lbrakk>write_reg TLBWired_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBWired_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBPageMask[liftState_simp]:
  "\<lbrakk>read_reg TLBPageMask_ref\<rbrakk>\<^sub>S = readS (TLBPageMask \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBPageMask[liftState_simp]:
  "\<lbrakk>write_reg TLBPageMask_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBPageMask_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBContext[liftState_simp]:
  "\<lbrakk>read_reg TLBContext_ref\<rbrakk>\<^sub>S = readS (TLBContext \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBContext[liftState_simp]:
  "\<lbrakk>write_reg TLBContext_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBContext_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntryLo1[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryLo1_ref\<rbrakk>\<^sub>S = readS (TLBEntryLo1 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntryLo1[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryLo1_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntryLo1_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBEntryLo0[liftState_simp]:
  "\<lbrakk>read_reg TLBEntryLo0_ref\<rbrakk>\<^sub>S = readS (TLBEntryLo0 \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBEntryLo0[liftState_simp]:
  "\<lbrakk>write_reg TLBEntryLo0_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBEntryLo0_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBRandom[liftState_simp]:
  "\<lbrakk>read_reg TLBRandom_ref\<rbrakk>\<^sub>S = readS (TLBRandom \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBRandom[liftState_simp]:
  "\<lbrakk>write_reg TLBRandom_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBRandom_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBIndex[liftState_simp]:
  "\<lbrakk>read_reg TLBIndex_ref\<rbrakk>\<^sub>S = readS (TLBIndex \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBIndex[liftState_simp]:
  "\<lbrakk>write_reg TLBIndex_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBIndex_update (\<lambda>_. v)))"
  by (auto simp: liftState_write_reg_updateS register_defs)

lemma liftS_read_reg_TLBProbe[liftState_simp]:
  "\<lbrakk>read_reg TLBProbe_ref\<rbrakk>\<^sub>S = readS (TLBProbe \<circ> regstate)"
  by (auto simp: liftState_read_reg_readS register_defs)

lemma liftS_write_reg_TLBProbe[liftState_simp]:
  "\<lbrakk>write_reg TLBProbe_ref v\<rbrakk>\<^sub>S = updateS (regstate_update (TLBProbe_update (\<lambda>_. v)))"
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
