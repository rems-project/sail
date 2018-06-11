theory State_lemmas
  imports State State_lifting
begin

lemma All_liftState_dom: "liftState_dom (r, m)"
  by (induction m) (auto intro: liftState.domintros)
termination liftState using All_liftState_dom by auto

named_theorems liftState_simp

lemma liftState_bind[liftState_simp]:
  "liftState r (bind m f) = bindS (liftState r m) (liftState r \<circ> f)"
  by (induction m f rule: bind.induct) auto

lemma liftState_return[liftState_simp]: "liftState r (return a) = returnS a" by (auto simp: return_def)

lemma Value_liftState_Run:
  assumes "(Value a, s') \<in> liftState r m s"
  obtains t where "Run m t a"
  by (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>;
      auto simp add: failS_def throwS_def returnS_def simp del: read_regvalS.simps;
      blast elim: Value_bindS_elim)

lemmas liftState_if_distrib[liftState_simp] = if_distrib[where f = "liftState ra" for ra]

lemma liftState_throw[liftState_simp]: "liftState r (throw e) = throwS e"
  by (auto simp: throw_def)
lemma liftState_assert[liftState_simp]: "liftState r (assert_exp c msg) = assert_expS c msg"
  by (auto simp: assert_exp_def assert_expS_def)
lemma liftState_exit[liftState_simp]: "liftState r (exit0 ()) = exitS ()"
  by (auto simp: exit0_def exitS_def)
lemma liftState_exclResult[liftState_simp]: "liftState r (excl_result ()) = excl_resultS ()"
  by (auto simp: excl_result_def liftState_simp)
lemma liftState_barrier[liftState_simp]: "liftState r (barrier bk) = returnS ()"
  by (auto simp: barrier_def)
lemma liftState_footprint[liftState_simp]: "liftState r (footprint ()) = returnS ()"
  by (auto simp: footprint_def)
lemma liftState_undefined[liftState_simp]: "liftState r (undefined_bool ()) = undefined_boolS ()"
  by (auto simp: undefined_bool_def liftState_simp)
lemma liftState_maybe_fail[liftState_simp]: "liftState r (maybe_fail msg x) = maybe_failS msg x"
  by (auto simp: maybe_fail_def maybe_failS_def liftState_simp split: option.splits)
lemma liftState_and_boolM[liftState_simp]:
  "liftState r (and_boolM x y) = and_boolS (liftState r x) (liftState r y)"
  by (auto simp: and_boolM_def and_boolS_def liftState_simp cong: bindS_cong if_cong)
lemma liftState_or_boolM[liftState_simp]:
  "liftState r (or_boolM x y) = or_boolS (liftState r x) (liftState r y)"
  by (auto simp: or_boolM_def or_boolS_def liftState_simp cong: bindS_cong if_cong)

lemma liftState_try_catch[liftState_simp]:
  "liftState r (try_catch m h) = try_catchS (liftState r m) (liftState r \<circ> h)"
  by (induction m h rule: try_catch_induct) (auto simp: try_catchS_bindS_no_throw)

lemma liftState_early_return[liftState_simp]:
  "liftState r (early_return r) = early_returnS r"
  by (auto simp: early_return_def early_returnS_def liftState_simp)

lemma liftState_catch_early_return[liftState_simp]:
  "liftState r (catch_early_return m) = catch_early_returnS (liftState r m)"
  by (auto simp: catch_early_return_def catch_early_returnS_def sum.case_distrib liftState_simp cong: sum.case_cong)

lemma liftState_liftR[liftState_simp]:
  "liftState r (liftR m) = liftRS (liftState r m)"
  by (auto simp: liftR_def liftRS_def liftState_simp)

lemma liftState_try_catchR[liftState_simp]:
  "liftState r (try_catchR m h) = try_catchRS (liftState r m) (liftState r \<circ> h)"
  by (auto simp: try_catchR_def try_catchRS_def sum.case_distrib liftState_simp cong: sum.case_cong)

lemma liftState_read_mem_BC:
  assumes "unsigned_method BC_bitU_list (bits_of_method BCa a) = unsigned_method BCa a"
  shows "liftState r (read_mem BCa BCb rk a sz) = read_memS BCa BCb rk a sz"
  using assms
  by (auto simp: read_mem_def read_mem_bytes_def read_memS_def read_mem_bytesS_def maybe_failS_def liftState_simp split: option.splits)

lemma liftState_read_mem[liftState_simp]:
  "\<And>a. liftState r (read_mem BC_mword BC_mword rk a sz) = read_memS BC_mword BC_mword rk a sz"
  "\<And>a. liftState r (read_mem BC_bitU_list BC_bitU_list rk a sz) = read_memS BC_bitU_list BC_bitU_list rk a sz"
  by (auto simp: liftState_read_mem_BC)

lemma liftState_write_mem_ea_BC:
  assumes "unsigned_method BC_bitU_list (bits_of_method BCa a) = unsigned_method BCa a"
  shows "liftState r (write_mem_ea BCa rk a sz) = write_mem_eaS BCa rk a (nat sz)"
  using assms by (auto simp: write_mem_ea_def write_mem_eaS_def)

lemma liftState_write_mem_ea[liftState_simp]:
  "\<And>a. liftState r (write_mem_ea BC_mword rk a sz) = write_mem_eaS BC_mword rk a (nat sz)"
  "\<And>a. liftState r (write_mem_ea BC_bitU_list rk a sz) = write_mem_eaS BC_bitU_list rk a (nat sz)"
  by (auto simp: liftState_write_mem_ea_BC)

lemma liftState_write_mem_val:
  "liftState r (write_mem_val BC v) = write_mem_valS BC v"
  by (auto simp: write_mem_val_def write_mem_valS_def liftState_simp split: option.splits)

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
  using assms by (auto simp: write_reg_def updateS_def returnS_def bindS_readS)

lemma liftState_iter_aux[liftState_simp]:
  shows "liftState r (iter_aux i f xs) = iterS_aux i (\<lambda>i x. liftState r (f i x)) xs"
  by (induction i "\<lambda>i x. liftState r (f i x)" xs rule: iterS_aux.induct)
     (auto simp: liftState_simp cong: bindS_cong)

lemma liftState_iteri[liftState_simp]:
  "liftState r (iteri f xs) = iteriS (\<lambda>i x. liftState r (f i x)) xs"
  by (auto simp: iteri_def iteriS_def liftState_simp)

lemma liftState_iter[liftState_simp]:
  "liftState r (iter f xs) = iterS (liftState r \<circ> f) xs"
  by (auto simp: iter_def iterS_def liftState_simp)

lemma liftState_foreachM[liftState_simp]:
  "liftState r (foreachM xs vars body) = foreachS xs vars (\<lambda>x vars. liftState r (body x vars))"
  by (induction xs vars "\<lambda>x vars. liftState r (body x vars)" rule: foreachS.induct)
     (auto simp: liftState_simp cong: bindS_cong)

lemma whileS_dom_step:
  assumes "whileS_dom (vars, cond, body, s)"
    and "(Value True, s') \<in> cond vars s"
    and "(Value vars', s'') \<in> body vars s'"
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
      then show ?case using while while' that IH by auto
    qed auto
    then show ?case by (auto simp: liftState_simp)
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
      then show ?case using k until IH by (auto simp: comp_def liftState_simp)
    qed auto
  qed auto
qed

(* Simplification rules for monadic Boolean connectives *)

lemma if_return_return[simp]: "(if a then return True else return False) = return a" by auto

lemma and_boolM_simps[simp]:
  "and_boolM (return b) y = (if b then y else return False)"
  "and_boolM x (return True) = x"
  "and_boolM x (return False) = x \<bind> (\<lambda>_. return False)"
  "\<And>x y z. and_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. and_boolM (y r) z))"
  by (auto simp: and_boolM_def)

lemmas and_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolM x y" for y]

lemma or_boolM_simps[simp]:
  "or_boolM (return b) y = (if b then return True else y)"
  "or_boolM x (return True) = x \<bind> (\<lambda>_. return True)"
  "or_boolM x (return False) = x"
  "\<And>x y z. or_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. or_boolM (y r) z))"
  by (auto simp: or_boolM_def)

lemmas or_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolM x y" for y]

lemma if_returnS_returnS[simp]: "(if a then returnS True else returnS False) = returnS a" by auto

lemma and_boolS_simps[simp]:
  "and_boolS (returnS b) y = (if b then y else returnS False)"
  "and_boolS x (returnS True) = x"
  "and_boolS x (returnS False) = bindS x (\<lambda>_. returnS False)"
  "\<And>x y z. and_boolS (bindS x y) z = (bindS x (\<lambda>r. and_boolS (y r) z))"
  by (auto simp: and_boolS_def)

lemmas and_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolS x y" for y]

lemma or_boolS_simps[simp]:
  "or_boolS (returnS b) y = (if b then returnS True else y)"
  "or_boolS x (returnS True) = bindS x (\<lambda>_. returnS True)"
  "or_boolS x (returnS False) = x"
  "\<And>x y z. or_boolS (bindS x y) z = (bindS x (\<lambda>r. or_boolS (y r) z))"
  by (auto simp: or_boolS_def)

lemmas or_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolS x y" for y]

end
