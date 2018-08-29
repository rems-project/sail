theory Riscv_duopod_lemmas
  imports
    Sail.Sail2_values_lemmas
    Sail.Sail2_state_lemmas
    Riscv_duopod
begin

abbreviation liftS ("\<lbrakk>_\<rbrakk>\<^sub>S") where "liftS \<equiv> liftState (get_regval, set_regval)"

lemmas register_defs = get_regval_def set_regval_def Xs_ref_def nextPC_ref_def PC_ref_def

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
