theory Prompt_monad_extras
  imports Prompt_monad
begin

lemma All_bind_dom: "bind_dom (oc, f)"
  by (induction oc) (auto intro: bind.domintros; blast intro: bind.domintros)+

termination bind using All_bind_dom by auto

lemma bind_induct[case_names Done Read_mem Read_reg Write_memv Excl_res Write_ea Barrier Footprint Write_reg Escape Fail Error Exception Internal]:
  fixes m :: "('a, 'e) outcome" and f :: "'a \<Rightarrow> ('b, 'e) outcome"
  assumes "\<And>a f. P (Done a) f"
    and "\<And>rk addr sz k f. (\<And>v m' opt. (m', opt) = k v \<Longrightarrow> P m' f) \<Longrightarrow> P (Read_mem (rk, addr, sz) k) f"
    and "\<And>reg k f. (\<And>v m' opt. (m', opt) = k v \<Longrightarrow> P m' f) \<Longrightarrow> P (Read_reg reg k) f"
    and "\<And>val k f. (\<And>v m' opt. (m', opt) = k v \<Longrightarrow> P m' f) \<Longrightarrow> P (Write_memv val k) f"
    and "\<And>k f. (\<And>v m' opt. (m', opt) = k v \<Longrightarrow> P m' f) \<Longrightarrow> P (Excl_res k) f"
    and "\<And>wk addr sz m opt f. P m f \<Longrightarrow> P (Write_ea (wk, addr, sz) (m, opt)) f"
    and "\<And>bk m opt f. P m f \<Longrightarrow> P (Barrier bk (m, opt)) f"
    and "\<And>m opt f. P m f \<Longrightarrow> P (Footprint (m, opt)) f"
    and "\<And>reg val m opt f. P m f \<Longrightarrow> P (Write_reg (reg, val) (m, opt)) f"
    and "\<And>descr f. P (Escape descr) f"
    and "\<And>descr f. P (Fail descr) f" and "\<And>descr f. P (Error descr) f" and "\<And>e f. P (Exception e) f"
    and "\<And>i m opt f. P m f \<Longrightarrow> P (Internal i (m, opt)) f"
  shows "P m f"
  by (rule bind.induct[split_format (complete), OF assms]; blast)

datatype event =
  (* Request to read memory *)
    Read_mem read_kind address_lifted nat memory_value
  (* Write is imminent, at address lifted, of size nat *)
  | Write_ea write_kind address_lifted nat
  (* Request the result of store-exclusive *)
  | Excl_res bool
  (* Request to write memory at last signalled address. Memory value should be 8
     times the size given in ea signal *)
  | Write_memv memory_value bool
  (* Request a memory barrier *)
  | Barrier " barrier_kind "
  (* Tell the system to dynamically recalculate dependency footprint *)
  | Footprint
  (* Request to read register *)
  | Read_reg reg_name register_value
  (* Request to write register *)
  | Write_reg reg_name register_value
  | Internal " ( string option *  (unit \<Rightarrow> string)option) "

inductive_set T :: "(('a, 'e)outcome \<times> event \<times> ('a, 'e)outcome) set" where
  Read_mem: "\<exists>opt. k v = (m, opt) \<Longrightarrow> ((outcome.Read_mem (rk, addr, sz) k), Read_mem rk addr sz v, m) \<in> T"
| Write_ea: "\<exists>opt. k = (m, opt) \<Longrightarrow> ((outcome.Write_ea (rk, addr, sz) k), Write_ea rk addr sz, m) \<in> T"
| Excl_res: "\<exists>opt. k r = (m, opt) \<Longrightarrow> ((outcome.Excl_res k), Excl_res r, m) \<in> T"
| Write_memv: "\<exists>opt. k r = (m, opt) \<Longrightarrow> ((outcome.Write_memv v k), Write_memv v r, m) \<in> T"
| Barrier: "\<exists>opt. k = (m, opt) \<Longrightarrow> ((outcome.Barrier bk k), Barrier bk, m) \<in> T"
| Footprint: "\<exists>opt. k = (m, opt) \<Longrightarrow> ((outcome.Footprint k), Footprint, m) \<in> T"
| Read_reg: "\<exists>opt. k v = (m, opt) \<Longrightarrow> ((outcome.Read_reg r k), Read_reg r v, m) \<in> T"
| Write_reg: "\<exists>opt. k = (m, opt) \<Longrightarrow> ((outcome.Write_reg (r, v) k), Write_reg r v, m) \<in> T"
| Internal: "\<exists>opt. k = (m, opt) \<Longrightarrow> ((outcome.Internal descr k), Internal descr, m) \<in> T"

inductive_set Traces :: "(('a, 'r)outcome \<times> event list \<times> ('a, 'r)outcome) set" where
  Nil: "(s, [], s) \<in> Traces"
| Step: "\<lbrakk>(s, e, s'') \<in> T; (s'', t, s') \<in> Traces\<rbrakk> \<Longrightarrow> (s, e # t, s') \<in> Traces"

declare Traces.intros[intro]
declare T.intros[intro]

declare prod.splits[split]
(* lemma fst_case_bind[simp]: "fst (case k of (o1, x) \<Rightarrow> (bind o1 f, x)) = bind (fst k) f"
  by (cases k) auto *)

lemmas Traces_ConsI = T.intros[THEN Step, rotated]

inductive_cases Traces_NilE[elim]: "(s, [], s') \<in> Traces"
inductive_cases Traces_ConsE[elim]: "(s, e # t, s') \<in> Traces"

abbreviation Run :: "('a, 'r)outcome \<Rightarrow> event list \<Rightarrow> 'a \<Rightarrow> bool"
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
  assumes "bind m f = outcome.Done a"
  obtains a' where "m = outcome.Done a'" and "f a' = outcome.Done a"
  using assms by (auto elim: bind.elims)

lemma bind_T_cases:
  assumes "(bind m f, e, s') \<in> T"
  obtains (Done) a where "m = Done a"
  | (Bind) m' where "s' = bind m' f" and "(m, e, m') \<in> T"
proof cases
  assume D: "\<forall>a. m \<noteq> Done a"
  show thesis using assms proof cases
    case (Read_mem k v rk addr sz)
    then obtain k' where "m = outcome.Read_mem (rk, addr, sz) k'" using D by (cases m) auto
    then show ?thesis using Read_mem by (intro Bind[of "fst (k' v)"]) auto
  next
    case (Write_ea k rk addr sz)
    then obtain k' where "m = outcome.Write_ea (rk, addr, sz) k'" using D by (cases m) auto
    then show ?thesis using Write_ea by (intro Bind[of "fst k'"]) auto
  next
    case (Excl_res k r)
    then obtain k' where "m = outcome.Excl_res k'" using D by (cases m) auto
    then show ?thesis using Excl_res by (intro Bind[of "fst (k' r)"]) auto
  next
    case (Write_memv k r v)
    then obtain k' where "m = outcome.Write_memv v k'" using D by (cases m) auto
    then show ?thesis using Write_memv by (intro Bind[of "fst (k' r)"]) auto
  next
    case (Barrier k bk)
    then obtain k' where "m = outcome.Barrier bk k'" using D by (cases m) auto
    then show ?thesis using Barrier by (intro Bind[of "fst k'"]) auto
  next
    case (Footprint k)
    then obtain k' where "m = outcome.Footprint k'" using D by (cases m) auto
    then show ?thesis using Footprint by (intro Bind[of "fst k'"]) auto
  next
    case (Read_reg k v r)
    then obtain k' where "m = outcome.Read_reg r k'" using D by (cases m) auto
    then show ?thesis using Read_reg by (intro Bind[of "fst (k' v)"]) (auto split: prod.splits)
  next
    case (Write_reg k r v)
    then obtain k' where "m = outcome.Write_reg (r, v) k'" using D by (cases m) auto
    then show ?thesis using Write_reg by (intro Bind[of "fst k'"]) auto
  next
    case (Internal k descr)
    then obtain k' where "m = outcome.Internal descr k'" using D by (cases m) auto
    then show ?thesis using Internal by (intro Bind[of "fst k'"]) auto
  qed
qed auto

lemma Run_bindE:
  fixes m :: "('b, 'r) outcome" and a :: 'a
  assumes "Run (bind m f) t a"
  obtains tm am tf where "t = tm @ tf" and "Run m tm am" and "Run (f am) tf a"
proof (use assms in \<open>induction "bind m f" t "Done a :: ('a,'r) outcome" arbitrary: m rule: Traces.induct\<close>)
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

lemma Run_BarrierE[elim!]:
  assumes "Run (outcome.Barrier bk k) t a"
  obtains t' where "t = Barrier bk # t'" and "Run (fst k) t' a"
  using assms by cases (auto elim: T.cases)

lemma bind_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>t a. Run m2 t a \<Longrightarrow> f1 a = f2 a"
  shows "bind m1 f1 = bind m2 f2"
proof (unfold m, use f in \<open>induction m2 f1 arbitrary: f2 rule: bind_induct\<close>)
  case (Read_mem rk addr sz k f)
  have "bind m' f = bind m' f2" if k: "k v = (m', opt)" for v m' opt
    using k by (auto intro!: Read_mem.IH[of _ opt v] Read_mem.prems)
  then show ?case by auto
next
  case (Read_reg reg k f)
  have "bind m' f = bind m' f2" if k: "k v = (m', opt)" for v m' opt
    using k by (auto intro!: Read_reg.IH[of _ opt v] Read_reg.prems)
  then show ?case by auto
next
  case (Write_memv val k f)
  have "bind m' f = bind m' f2" if k: "k v = (m', opt)" for v m' opt
    using k by (auto intro!: Write_memv.IH[of _ opt v] Write_memv.prems)
  then show ?case by auto
next
  case (Excl_res k f)
  have "bind m' f = bind m' f2" if k: "k v = (m', opt)" for v m' opt
    using k by (auto intro!: Excl_res.IH[of _ opt v] Excl_res.prems)
  then show ?case by auto
next
  case (Write_ea wk addr sz m opt f)
  show ?case by (auto intro!: Write_ea)
next
  case (Barrier bk m opt f)
  show ?case by (auto intro!: Barrier)
next
  case (Footprint m opt f)
  show ?case by (auto intro!: Footprint)
next
  case (Write_reg reg val m opt f)
  show ?case by (auto intro!: Write_reg)
next
  case (Internal i m opt f)
  show ?case by (auto intro!: Internal)
qed auto

end
