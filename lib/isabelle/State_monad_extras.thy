theory State_monad_extras
  imports State_monad
begin

lemma bind_ext_cong[fundef_cong]:
  assumes m: "m1 s = m2 s"
    and f: "\<And>a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "(bind m1 f1) s = (bind m2 f2) s"
proof -
  have "List.concat (map (\<lambda>x. case x of (Value a, s') \<Rightarrow> f1 a s' | (Exception0 e, s') \<Rightarrow> [(Exception0 e, s')]) (m2 s)) =
        List.concat (map (\<lambda>x. case x of (Value a, s') \<Rightarrow> f2 a s' | (Exception0 e, s') \<Rightarrow> [(Exception0 e, s')]) (m2 s))"
    using f by (intro arg_cong[where f = List.concat]) (auto intro: map_ext split: result.splits)
  then show ?thesis using m by (auto simp: bind_def)
qed

lemma bind_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>s a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bind m1 f1 = bind m2 f2"
  using assms by (blast intro: bind_ext_cong)

lemma bind_return[simp]: "bind (return x) m = m x"
  by (auto simp add: bind_def return_def)

end
