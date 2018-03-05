theory Prompt_monad_lemmas
  imports
    Prompt_monad
    Sail_values_lemmas
begin

lemma All_bind_dom: "bind_dom (m, f)"
  by (induction m) (auto intro: bind.domintros)

termination bind using All_bind_dom by auto
lemmas bind_induct[case_names Done Read_mem Write_memv Read_reg Excl_res Write_ea Barrier Write_reg Fail Error Exception] = bind.induct

lemma bind_return[simp]: "bind (return a) f = f a"
  by (auto simp: return_def)

lemma bind_assoc[simp]: "bind (bind m f) g = bind m (\<lambda>x. bind (f x) g)"
  by (induction m f arbitrary: g rule: bind.induct) auto

lemma All_try_catch_dom: "try_catch_dom (m, h)"
  by (induction m) (auto intro: try_catch.domintros)
termination try_catch using All_try_catch_dom by auto
lemmas try_catch_induct[case_names Done Read_mem Write_memv Read_reg Excl_res Write_ea Barrier Write_reg Fail Error Exception] = try_catch.induct

datatype 'regval event =
  (* Request to read memory *)
    e_read_mem read_kind "bitU list" nat "memory_byte list"
  | e_read_tag "bitU list" bitU
  (* Write is imminent, at address lifted, of size nat *)
  | e_write_ea write_kind "bitU list" nat
  (* Request the result of store-exclusive *)
  | e_excl_res bool
  (* Request to write memory at last signalled address. Memory value should be 8
     times the size given in ea signal *)
  | e_write_memv "memory_byte list" bool
  | e_write_tagv bitU bool
  (* Tell the system to dynamically recalculate dependency footprint *)
  | e_footprint
  (* Request a memory barrier *)
  | e_barrier " barrier_kind "
  (* Request to read register *)
  | e_read_reg string 'regval
  (* Request to write register *)
  | e_write_reg string 'regval
  | e_undefined bool
  | e_print string

inductive_set T :: "(('rv, 'a, 'e) monad \<times> 'rv event \<times> ('rv, 'a, 'e) monad) set" where
  Read_mem: "((Read_mem rk addr sz k), e_read_mem rk addr sz v, k v) \<in> T"
| Read_tag: "((Read_tag addr k), e_read_tag addr v, k v) \<in> T"
| Write_ea: "((Write_ea wk addr sz k), e_write_ea wk addr sz, k) \<in> T"
| Excl_res: "((Excl_res k), e_excl_res r, k r) \<in> T"
| Write_memv: "((Write_memv v k), e_write_memv v r, k r) \<in> T"
| Write_tagv: "((Write_tagv v k), e_write_tagv v r, k r) \<in> T"
| Footprint: "((Footprint k), e_footprint, k) \<in> T"
| Barrier: "((Barrier bk k), e_barrier bk, k) \<in> T"
| Read_reg: "((Read_reg r k), e_read_reg r v, k v) \<in> T"
| Write_reg: "((Write_reg r v k), e_write_reg r v, k) \<in> T"
| Undefined : "((Undefined k), e_undefined v, k v) \<in> T"
| Print: "((Print msg k), e_print msg, k) \<in> T"

inductive_set Traces :: "(('rv, 'a, 'e) monad \<times> 'rv event list \<times> ('rv, 'a, 'e) monad) set" where
  Nil: "(s, [], s) \<in> Traces"
| Step: "\<lbrakk>(s, e, s'') \<in> T; (s'', t, s') \<in> Traces\<rbrakk> \<Longrightarrow> (s, e # t, s') \<in> Traces"

declare Traces.intros[intro]
declare T.intros[intro]

declare prod.splits[split]

lemmas Traces_ConsI = T.intros[THEN Step, rotated]

inductive_cases Traces_NilE[elim]: "(s, [], s') \<in> Traces"
inductive_cases Traces_ConsE[elim]: "(s, e # t, s') \<in> Traces"

lemma Traces_cases:
  fixes m :: "('rv, 'a, 'e) monad"
  assumes Run: "(m, t, m') \<in> Traces"
  obtains (Nil) a where "m = m'" and "t = []"
  | (Read_mem) rk addr s k t' v where "m = Read_mem rk addr s k" and "t = e_read_mem rk addr s v # t'" and "(k v, t', m') \<in> Traces"
  | (Read_tag) addr k t' v where "m = Read_tag addr k" and "t = e_read_tag addr v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_memv) val k t' v where "m = Write_memv val k" and "t = e_write_memv val v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_tagv) val k t' v where "m = Write_tagv val k" and "t = e_write_tagv val v # t'" and "(k v, t', m') \<in> Traces"
  | (Barrier) bk k t' v where "m = Barrier bk k" and "t = e_barrier bk # t'" and "(k, t', m') \<in> Traces"
  | (Read_reg) reg k t' v where "m = Read_reg reg k" and "t = e_read_reg reg v # t'" and "(k v, t', m') \<in> Traces"
  | (Excl_res) k t' v where "m = Excl_res k" and "t = e_excl_res v # t'" and "(k v, t', m') \<in> Traces"
  | (Write_ea) wk addr s k t' where "m = Write_ea wk addr s k" and "t = e_write_ea wk addr s # t'" and "(k, t', m') \<in> Traces"
  | (Footprint) k t' where "m = Footprint k" and "t = e_footprint # t'" and "(k, t', m') \<in> Traces"
  | (Write_reg) reg v k t' where "m = Write_reg reg v k" and "t = e_write_reg reg v # t'" and "(k, t', m') \<in> Traces"
  | (Undefined) v k t' where "m = Undefined k" and "t = e_undefined v # t'" and "(k v, t', m') \<in> Traces"
  | (Print) msg k t' where "m = Print msg k" and "t = e_print msg # t'" and "(k, t', m') \<in> Traces"
proof (use Run in \<open>cases m t m' set: Traces\<close>)
  case Nil
  then show ?thesis by (auto intro: that(1))
next
  case (Step e m'' t')
  from \<open>(m, e, m'') \<in> T\<close> and \<open>t = e # t'\<close> and \<open>(m'', t', m') \<in> Traces\<close>
  show ?thesis by (cases m e m'' rule: T.cases; elim that; blast)
qed

abbreviation Run :: "('rv, 'a, 'e) monad \<Rightarrow> 'rv event list \<Rightarrow> 'a \<Rightarrow> bool"
  where "Run s t a \<equiv> (s, t, Done a) \<in> Traces"

lemma Run_appendI:
  assumes "(s, t1, s') \<in> Traces"
    and "Run s' t2 a"
  shows "Run s (t1 @ t2) a"
proof (use assms in \<open>induction t1 arbitrary: s\<close>)
  case (Cons e t1)
  then show ?case by (elim Traces_ConsE) auto
qed auto

lemma bind_DoneE:
  assumes "bind m f = Done a"
  obtains a' where "m = Done a'" and "f a' = Done a"
  using assms by (auto elim: bind.elims)

lemma bind_T_cases:
  assumes "(bind m f, e, s') \<in> T"
  obtains (Done) a where "m = Done a"
  | (Bind) m' where "s' = bind m' f" and "(m, e, m') \<in> T"
  using assms by (cases; blast elim: bind.elims)

lemma Run_bindE:
  fixes m :: "('rv, 'b, 'e) monad" and a :: 'a
  assumes "Run (bind m f) t a"
  obtains tm am tf where "t = tm @ tf" and "Run m tm am" and "Run (f am) tf a"
proof (use assms in \<open>induction "bind m f" t "Done a :: ('rv, 'a, 'e) monad" arbitrary: m rule: Traces.induct\<close>)
  case Nil
  obtain am where "m = Done am" and "f am = Done a" using Nil(1) by (elim bind_DoneE)
  then show ?case by (intro Nil(2)) auto
next
  case (Step e s'' t m)
  show thesis using Step(1)
  proof (cases rule: bind_T_cases)
    case (Done am)
    then show ?thesis using Step(1,2) by (intro Step(4)[of "[]" "e # t" am]) auto
  next
    case (Bind m')
    show ?thesis proof (rule Step(3)[OF Bind(1)])
      fix tm tf am
      assume "t = tm @ tf" and "Run m' tm am" and "Run (f am) tf a"
      then show thesis using Bind by (intro Step(4)[of "e # tm" tf am]) auto
    qed
  qed
qed

lemma Run_DoneE:
  assumes "Run (Done a) t a'"
  obtains "t = []" and "a' = a"
  using assms by (auto elim: Traces.cases T.cases)

lemma Run_Done_iff_Nil[simp]: "Run (Done a) t a' \<longleftrightarrow> t = [] \<and> a' = a"
  by (auto elim: Run_DoneE)

lemma bind_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>t a. Run m2 t a \<Longrightarrow> f1 a = f2 a"
  shows "bind m1 f1 = bind m2 f2"
  unfolding m using f
  by (induction m2 f1 arbitrary: f2 rule: bind.induct; unfold bind.simps; blast)

end
