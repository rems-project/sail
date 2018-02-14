theory State_extras
  imports State
begin

lemma All_liftState_dom: "liftState_dom (r, m)"
  by (induction m) (auto intro: liftState.domintros)

termination liftState using All_liftState_dom by auto

lemma liftState_return[simp]: "liftState r (return a) = returnS a" by (auto simp: return_def)
lemma liftState_throw[simp]: "liftState r (throw e) = throwS e" by (auto simp: throw_def)
lemma liftState_assert[simp]: "liftState r (assert_exp c msg) = assert_expS c msg" by (auto simp: assert_exp_def assert_expS_def)

lemma liftState_bind[simp]:
  "liftState r (bind m f) = bindS (liftState r m) (liftState r \<circ> f)"
  by (induction m f rule: bind.induct) auto

lemma liftState_read_reg[intro]:
  assumes "\<And>s. Option.bind (get_regval' (name reg) s) (of_regval reg) = Some (read_from reg s)"
  shows "liftState (get_regval', set_regval') (read_reg reg) = read_regS reg"
proof
  fix s :: "'a sequential_state"
  obtain rv v where "get_regval' (name reg) (regstate s) = Some rv"
    and "of_regval reg rv = Some v" and "read_from reg (regstate s) = v"
    using assms unfolding bind_eq_Some_conv by blast
  then show "liftState (get_regval', set_regval') (read_reg reg) s = read_regS reg s"
    by (auto simp: read_reg_def bindS_def returnS_def read_regS_def)
qed

lemma liftState_write_reg[intro]:
  assumes "\<And>s. set_regval' (name reg) (regval_of reg v) s = Some (write_to reg s v)"
  shows "liftState (get_regval', set_regval') (write_reg reg v) = write_regS reg v"
  using assms by (auto simp: write_reg_def bindS_def returnS_def write_regS_def)

end
