theory State_monad_extras
  imports State_monad
begin

abbreviation "bindS_aux f \<equiv> (\<lambda>r. case r of (Value a, s') \<Rightarrow> f a s' | (Ex e, s') \<Rightarrow> [(Ex e, s')])"

lemma bindS_ext_cong[fundef_cong]:
  assumes m: "m1 s = m2 s"
    and f: "\<And>a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "(bindS m1 f1) s = (bindS m2 f2) s"
proof -
  have "List.concat (map (bindS_aux f1) (m2 s)) = List.concat (map (bindS_aux f2) (m2 s))"
    using f by (intro arg_cong[where f = List.concat]) (auto intro: map_ext split: result.splits)
  then show ?thesis using m by (auto simp: bindS_def)
qed

lemma bindS_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>s a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 = bindS m2 f2"
  using assms by (blast intro: bindS_ext_cong)

lemma bindS_returnS[simp]: "bindS (returnS x) m = m x"
  by (auto simp add: bindS_def returnS_def)

lemma bindS_assoc[simp]: "bindS (bindS m f) g = bindS m (\<lambda>x. bindS (f x) g)"
proof -
  have "List.concat (map (bindS_aux g) (List.concat (map (bindS_aux f) xs))) =
        List.concat (map (bindS_aux (\<lambda>x s. List.concat (map (bindS_aux g) (f x s)))) xs)" for xs
    by (induction xs) (auto split: result.splits)
  then show ?thesis unfolding bindS_def by auto
qed

lemma bindS_failS[simp]: "bindS (failS msg) f = failS msg" by (auto simp: bindS_def failS_def)
lemma bindS_throwS[simp]: "bindS (throwS e) f = throwS e" by (auto simp: bindS_def throwS_def)
declare seqS_def[simp]

lemma try_catchS_returnS[simp]: "try_catchS (returnS a) h = returnS a"
  and try_catchS_failS[simp]: "try_catchS (failS msg) h = failS msg"
  and try_catchS_throwS[simp]: "try_catchS (throwS e) h = h e"
  by (auto simp: returnS_def failS_def throwS_def try_catchS_def)

end
