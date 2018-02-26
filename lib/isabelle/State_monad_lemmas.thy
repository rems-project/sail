theory State_monad_lemmas
  imports
    State_monad
    Sail_values_lemmas
begin

context
  notes returnS_def[simp] and failS_def[simp] and throwS_def[simp] and readS_def[simp] and updateS_def[simp]
begin

abbreviation "bindS_aux f \<equiv> (\<lambda>r. case r of (Value a, s') \<Rightarrow> f a s' | (Ex e, s') \<Rightarrow> [(Ex e, s')])"
abbreviation "bindS_app ms f \<equiv> List.concat (List.map (bindS_aux f) ms)"

lemma bindS_ext_cong[fundef_cong]:
  assumes m: "m1 s = m2 s"
    and f: "\<And>a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 s = bindS m2 f2 s"
proof -
  have "bindS_app (m2 s) f1 = bindS_app (m2 s) f2"
    using f by (intro arg_cong[where f = List.concat]) (auto intro: map_ext split: result.splits)
  then show ?thesis using m by (auto simp: bindS_def)
qed

lemma bindS_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>s a s'. (Value a, s') \<in> set (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 = bindS m2 f2"
  using assms by (blast intro: bindS_ext_cong)

lemma bindS_returnS_left[simp]: "bindS (returnS x) f = f x"
  by (auto simp add: bindS_def)

lemma bindS_returnS_right[simp]: "bindS m returnS = (m :: ('regs, 'a, 'e) monadS)"
proof -
  have "List.concat (map (bindS_aux returnS) ms) = ms" for ms :: "(('a, 'e) result \<times> 'regs sequential_state) list"
    by (induction ms) (auto split: result.splits)
  then show ?thesis unfolding bindS_def by blast
qed

lemma bindS_readS: "bindS (readS f) m = (\<lambda>s. m (f s) s)"
  by (auto simp: bindS_def)

lemma bindS_updateS: "bindS (updateS f) m = (\<lambda>s. m () (f s))"
  by (auto simp: bindS_def)

lemma bindS_assoc[simp]: "bindS (bindS m f) g = bindS m (\<lambda>x. bindS (f x) g)"
proof -
  have "List.concat (map (bindS_aux g) (List.concat (map (bindS_aux f) xs))) =
        List.concat (map (bindS_aux (\<lambda>x s. List.concat (map (bindS_aux g) (f x s)))) xs)" for xs
    by (induction xs) (auto split: result.splits)
  then show ?thesis unfolding bindS_def by auto
qed

lemma bindS_failS[simp]: "bindS (failS msg) f = failS msg" by (auto simp: bindS_def)
lemma bindS_throwS[simp]: "bindS (throwS e) f = throwS e" by (auto simp: bindS_def)
declare seqS_def[simp]

lemma Value_bindS_elim:
  assumes "(Value a, s') \<in> set (bindS m f s)"
  obtains s'' a' where "(Value a', s'') \<in> set (m s)" and "(Value a, s') \<in> set (f a' s'')"
  using assms by (auto simp: bindS_def; split result.splits; auto)

abbreviation
  "try_catchS_aux h r \<equiv>
    (case r of
       (Value a, s') => returnS a s'
     | (Ex (Throw e), s') => h e s'
     | (Ex (Failure msg), s') => [(Ex (Failure msg), s')])"
abbreviation "try_catchS_app ms h \<equiv> List.concat (List.map (try_catchS_aux h) ms)"

lemma try_catchS_returnS[simp]: "try_catchS (returnS a) h = returnS a"
  and try_catchS_failS[simp]: "try_catchS (failS msg) h = failS msg"
  and try_catchS_throwS[simp]: "try_catchS (throwS e) h = h e"
  by (auto simp: try_catchS_def)

lemma try_catchS_cong[cong]:
  assumes "\<And>s. m1 s = m2 s" and "\<And>e s. h1 e s = h2 e s"
  shows "try_catchS m1 h1 = try_catchS m2 h2"
  using assms by (intro arg_cong2[where f = try_catchS] ext) auto

fun ignore_throw_app :: "(('a, 'e1) result \<times> 's) list \<Rightarrow> (('a, 'e2) result \<times> 's) list" where
  "ignore_throw_app [] = []"
| "ignore_throw_app ((Value a, s) # ms) = (Value a, s) # ignore_throw_app ms"
| "ignore_throw_app ((Ex (Failure msg), s) # ms) = (Ex (Failure msg), s) # ignore_throw_app ms"
| "ignore_throw_app ((Ex (Throw e), s) # ms) = ignore_throw_app ms"
abbreviation ignore_throw :: "('r, 'a, 'e1) monadS \<Rightarrow> ('r, 'a, 'e2) monadS" where
  "ignore_throw m \<equiv> \<lambda>s. ignore_throw_app (m s)"

lemma [simp]: "ignore_throw_app ms = (Ex (Throw e), s) # ms' \<longleftrightarrow> False"
  by (induction ms rule: ignore_throw_app.induct) auto

lemma ignore_throw_app_append[simp]:
  "ignore_throw_app (ms1 @ ms2) = ignore_throw_app ms1 @ ignore_throw_app ms2"
  by (induction ms1 rule: ignore_throw_app.induct) auto

lemma ignore_throw_app_bindS_app[simp]:
  "ignore_throw_app (bindS_app ms f) = bindS_app (ignore_throw_app ms) (ignore_throw \<circ> f)"
  by (induction ms rule: ignore_throw_app.induct) (auto split: result.splits)

lemma ignore_throw_bindS[simp]:
  "ignore_throw (bindS m f) = bindS (ignore_throw m) (ignore_throw \<circ> f)"
  "ignore_throw (bindS m f) s = bindS (ignore_throw m) (ignore_throw \<circ> f) s"
  unfolding bindS_def by auto

lemma try_catchS_bindS_no_throw:
  fixes m1 :: "('r, 'a, 'e1) monadS" and m2 :: "('r, 'a, 'e2) monadS"
  assumes m1: "\<And>s. ignore_throw m1 s = m1 s"
    and m2: "\<And>s. ignore_throw m1 s = m2 s"
  shows "try_catchS (bindS m1 f) h = bindS m2 (\<lambda>a. try_catchS (f a) h)"
proof
  fix s
  have 1: "try_catchS_app (bindS_app ms f) h =
        bindS_app (ignore_throw_app ms) (\<lambda>a s'. try_catchS_app (f a s') h)"
    if "ignore_throw_app ms = ms" for ms
    using that by (induction ms rule: ignore_throw_app.induct) auto
  then show "try_catchS (bindS m1 f) h s = bindS m2 (\<lambda>a. try_catchS (f a) h) s"
    using m1 unfolding try_catchS_def bindS_def m2[symmetric] by blast
qed

lemma no_throw_mem_builtins:
  "\<And>a. ignore_throw (returnS a) = returnS a"
  "\<And>BC rk a sz s. ignore_throw (read_mem_bytesS BC rk a sz) s = read_mem_bytesS BC rk a sz s"
  "\<And>BC a s. ignore_throw (read_tagS BC a) s = read_tagS BC a s"
  "\<And>BC wk a sz s. ignore_throw (write_mem_eaS BC wk a sz) s = write_mem_eaS BC wk a sz s"
  "\<And>v s. ignore_throw (write_mem_bytesS v) s = write_mem_bytesS v s"
  "\<And>BC v s. ignore_throw (write_mem_valS BC v) s = write_mem_valS BC v s"
  "\<And>t s. ignore_throw (write_tagS t) s = write_tagS t s"
  "\<And>s. ignore_throw (excl_resultS ()) s = excl_resultS () s"
  unfolding read_mem_bytesS_def read_memS_def read_tagS_def write_mem_eaS_def write_mem_valS_def write_mem_bytesS_def write_tagS_def excl_resultS_def
  by (auto simp: bindS_def chooseS_def Let_def split: option.splits)+

lemma no_throw_read_memS: "ignore_throw (read_memS BCa BCb rk a sz) s = read_memS BCa BCb rk a sz s"
  by (auto simp: read_memS_def no_throw_mem_builtins cong: bindS_cong)

lemma no_throw_read_regvalS: "ignore_throw (read_regvalS r reg_name) s = read_regvalS r reg_name s"
  by (cases r) (auto simp: bindS_def split: option.splits)

lemma no_throw_write_regvalS: "ignore_throw (write_regvalS r reg_name v) s = write_regvalS r reg_name v s"
  by (cases r) (auto simp: bindS_def split: option.splits)

lemmas no_throw_builtins[simp, intro] =
  no_throw_mem_builtins no_throw_read_regvalS no_throw_write_regvalS no_throw_read_memS

end

end
