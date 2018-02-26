theory State_lemmas
  imports State
begin

lemma All_liftState_dom: "liftState_dom (r, m)"
  by (induction m) (auto intro: liftState.domintros)
termination liftState using All_liftState_dom by auto

lemma liftState_bind[simp]:
  "liftState r (bind m f) = bindS (liftState r m) (liftState r \<circ> f)"
  by (induction m f rule: bind.induct) auto

lemma liftState_return[simp]: "liftState r (return a) = returnS a" by (auto simp: return_def)

lemma Value_liftState_Run:
  assumes "(Value a, s') \<in> set (liftState r m s)"
  obtains t where "Run m t a"
  by (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>;
      auto simp add: failS_def throwS_def returnS_def simp del: read_regvalS.simps;
      blast elim: Value_bindS_elim)

lemma liftState_throw[simp]: "liftState r (throw e) = throwS e" by (auto simp: throw_def)
lemma liftState_assert[simp]: "liftState r (assert_exp c msg) = assert_expS c msg" by (auto simp: assert_exp_def assert_expS_def)
lemma liftState_exit[simp]: "liftState r (exit0 ()) = exitS ()" by (auto simp: exit0_def exitS_def)
lemma liftState_exclResult[simp]: "liftState r (excl_result ()) = excl_resultS ()" by (auto simp: excl_result_def)
lemma liftState_barrier[simp]: "liftState r (barrier bk) = returnS ()" by (auto simp: barrier_def)
lemma liftState_footprint[simp]: "liftState r (footprint ()) = returnS ()" by (auto simp: footprint_def)

lemma liftState_try_catch[simp]:
  "liftState r (try_catch m h) = try_catchS (liftState r m) (liftState r \<circ> h)"
  by (induction m h rule: try_catch_induct) (auto simp: try_catchS_bindS_no_throw)

lemma liftState_early_return[simp]:
  "liftState r (early_return r) = early_returnS r"
  by (auto simp: early_return_def early_returnS_def)

lemma liftState_catch_early_return[simp]:
  "liftState r (catch_early_return m) = catch_early_returnS (liftState r m)"
  by (auto simp: catch_early_return_def catch_early_returnS_def sum.case_distrib cong: sum.case_cong)

lemma liftState_liftR[simp]:
  "liftState r (liftR m) = liftSR (liftState r m)"
  by (auto simp: liftR_def liftSR_def)

lemma liftState_try_catchR[simp]:
  "liftState r (try_catchR m h) = try_catchSR (liftState r m) (liftState r \<circ> h)"
  by (auto simp: try_catchR_def try_catchSR_def sum.case_distrib cong: sum.case_cong)

lemma liftState_read_mem_BC[simp]:
  assumes "unsigned_method BC_bitU_list (bits_of_method BCa a) = unsigned_method BCa a"
  shows "liftState r (read_mem BCa BCb rk a sz) = read_memS BCa BCb rk a sz"
  using assms by (auto simp: read_mem_def read_memS_def read_mem_bytesS_def)
lemmas liftState_read_mem[simp] =
  liftState_read_mem_BC[OF unsigned_bits_of_mword] liftState_read_mem_BC[OF unsigned_bits_of_bitU_list]

lemma liftState_write_mem_ea_BC:
  assumes "unsigned_method BC_bitU_list (bits_of_method BCa a) = unsigned_method BCa a"
  shows "liftState r (write_mem_ea BCa rk a sz) = write_mem_eaS BCa rk a sz"
  using assms by (auto simp: write_mem_ea_def write_mem_eaS_def)
lemmas liftState_write_mem_ea[simp] =
  liftState_write_mem_ea_BC[OF unsigned_bits_of_mword] liftState_write_mem_ea_BC[OF unsigned_bits_of_bitU_list]

lemma liftState_write_mem_val:
  "liftState r (write_mem_val BC v) = write_mem_valS BC v"
  by (auto simp: write_mem_val_def write_mem_valS_def split: option.splits)

lemma liftState_read_reg_readS:
  assumes "\<And>s. Option.bind (get_regval' (name reg) s) (of_regval reg) = Some (read_from reg s)"
  shows "liftState (get_regval', set_regval') (read_reg reg) = readS (read_from reg \<circ> regstate)"
proof
  fix s :: "'a sequential_state"
  obtain rv v where "get_regval' (name reg) (regstate s) = Some rv"
    and "of_regval reg rv \<equiv> Some v" and "read_from reg (regstate s) = v"
    using assms unfolding bind_eq_Some_conv by blast
  then show "liftState (get_regval', set_regval') (read_reg reg) s = readS (read_from reg \<circ> regstate) s"
    by (auto simp: read_reg_def bindS_def returnS_def read_regS_def readS_def)
qed

lemma liftState_write_reg_updateS:
  assumes "\<And>s. set_regval' (name reg) (regval_of reg v) s = Some (write_to reg v s)"
  shows "liftState (get_regval', set_regval') (write_reg reg v) = updateS (regstate_update (write_to reg v))"
  using assms by (auto simp: write_reg_def bindS_readS updateS_def returnS_def)

lemma liftState_iter_aux[simp]:
  shows "liftState r (iter_aux i f xs) = iterS_aux i (\<lambda>i x. liftState r (f i x)) xs"
  by (induction i "\<lambda>i x. liftState r (f i x)" xs rule: iterS_aux.induct) (auto cong: bindS_cong)

lemma liftState_iteri[simp]:
  "liftState r (iteri f xs) = iteriS (\<lambda>i x. liftState r (f i x)) xs"
  by (auto simp: iteri_def iteriS_def)

lemma liftState_iter[simp]:
  "liftState r (iter f xs) = iterS (liftState r \<circ> f) xs"
  by (auto simp: iter_def iterS_def)

lemma liftState_foreachM[simp]:
  "liftState r (foreachM xs vars body) = foreachS xs vars (\<lambda>x vars. liftState r (body x vars))"
  by (induction xs vars "\<lambda>x vars. liftState r (body x vars)" rule: foreachS.induct)
     (auto cong: bindS_cong)

lemma whileS_dom_step:
  assumes "whileS_dom (vars, cond, body, s)"
    and "(Value True, s') \<in> set (cond vars s)"
    and "(Value vars', s'') \<in> set (body vars s')"
  shows "whileS_dom (vars', cond, body, s'')"
  by (use assms in \<open>induction vars cond body s arbitrary: vars' s' s'' rule: whileS.pinduct\<close>)
     (auto intro: whileS.domintros)

lemma whileM_dom_step:
  assumes "whileM_dom (vars, cond, body)"
    and "Run (cond vars) t True"
    and "Run (body vars) t' vars'"
  shows "whileM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: whileM.pinduct\<close>)
     (auto intro: whileM.domintros)

lemma whileM_dom_ex_step:
  assumes "whileM_dom (vars, cond, body)"
    and "\<exists>t. Run (cond vars) t True"
    and "\<exists>t'. Run (body vars) t' vars'"
  shows "whileM_dom (vars', cond, body)"
  using assms by (blast intro: whileM_dom_step)

lemmas whileS_pinduct = whileS.pinduct[case_names Step]

lemma liftState_whileM:
  assumes "whileS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
    and "whileM_dom (vars, cond, body)"
  shows "liftState r (whileM vars cond body) s = whileS vars (liftState r \<circ> cond) (liftState r \<circ> body) s"
proof (use assms in \<open>induction vars "liftState r \<circ> cond" "liftState r \<circ> body" s rule: whileS.pinduct\<close>)
  case Step: (1 vars s)
  note domS = Step(1) and IH = Step(2) and domM = Step(3)
  show ?case unfolding whileS.psimps[OF domS] whileM.psimps[OF domM] liftState_bind
  proof (intro bindS_ext_cong, goal_cases cond while)
    case (while a s')
    have "bindS (liftState r (body vars)) (liftState r \<circ> (\<lambda>vars. whileM vars cond body)) s' =
          bindS (liftState r (body vars)) (\<lambda>vars. whileS vars (liftState r \<circ> cond) (liftState r \<circ> body)) s'"
      if "a"
    proof (intro bindS_ext_cong, goal_cases body while')
      case (while' vars' s'')
      have "whileM_dom (vars', cond, body)" proof (rule whileM_dom_ex_step[OF domM])
        show "\<exists>t. Run (cond vars) t True" using while that by (auto elim: Value_liftState_Run)
        show "\<exists>t'. Run (body vars) t' vars'" using while' that by (auto elim: Value_liftState_Run)
      qed
      then show ?case using while while' that by (auto intro: IH)
    qed auto
    then show ?case by auto
  qed auto
qed


lemma untilM_dom_step:
  assumes "untilM_dom (vars, cond, body)"
    and "Run (body vars) t vars'"
    and "Run (cond vars') t' False"
  shows "untilM_dom (vars', cond, body)"
  by (use assms in \<open>induction vars cond body arbitrary: vars' t t' rule: untilM.pinduct\<close>)
     (auto intro: untilM.domintros)

lemma untilM_dom_ex_step:
  assumes "untilM_dom (vars, cond, body)"
    and "\<exists>t. Run (body vars) t vars'"
    and "\<exists>t'. Run (cond vars') t' False"
  shows "untilM_dom (vars', cond, body)"
  using assms by (blast intro: untilM_dom_step)

lemma liftState_untilM:
  assumes "untilS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
    and "untilM_dom (vars, cond, body)"
  shows "liftState r (untilM vars cond body) s = untilS vars (liftState r \<circ> cond) (liftState r \<circ> body) s"
proof (use assms in \<open>induction vars "liftState r \<circ> cond" "liftState r \<circ> body" s rule: untilS.pinduct\<close>)
  case Step: (1 vars s)
  note domS = Step(1) and IH = Step(2) and domM = Step(3)
  show ?case unfolding untilS.psimps[OF domS] untilM.psimps[OF domM] liftState_bind
  proof (intro bindS_ext_cong, goal_cases body k)
    case (k vars' s')
    show ?case unfolding comp_def liftState_bind
    proof (intro bindS_ext_cong, goal_cases cond until)
      case (until a s'')
      have "untilM_dom (vars', cond, body)" if "\<not>a"
      proof (rule untilM_dom_ex_step[OF domM])
        show "\<exists>t. Run (body vars) t vars'" using k by (auto elim: Value_liftState_Run)
        show "\<exists>t'. Run (cond vars') t' False" using until that by (auto elim: Value_liftState_Run)
      qed
      then show ?case using k until IH by (auto simp: comp_def)
    qed auto
  qed auto
qed

end
