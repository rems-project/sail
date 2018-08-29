(*========================================================================*)
(*                        Lem                                             *)
(*                                                                        *)
(*          Dominic Mulligan, University of Cambridge                     *)
(*          Francesco Zappa Nardelli, INRIA Paris-Rocquencourt            *)
(*          Gabriel Kerneis, University of Cambridge                      *)
(*          Kathy Gray, University of Cambridge                           *)
(*          Peter Boehm, University of Cambridge (while working on Lem)   *)
(*          Peter Sewell, University of Cambridge                         *)
(*          Scott Owens, University of Kent                               *)
(*          Thomas Tuerk, University of Cambridge                         *)
(*          Brian Campbell, University of Edinburgh                       *)
(*          Shaked Flur, University of Cambridge                          *)
(*          Thomas Bauereiss, University of Cambridge                     *)
(*          Stephen Kell, University of Cambridge                         *)
(*          Thomas Williams                                               *)
(*          Lars Hupel                                                    *)
(*          Basile Clement                                                *)
(*                                                                        *)
(*  The Lem sources are copyright 2010-2018                               *)
(*  by the authors above and Institut National de Recherche en            *)
(*  Informatique et en Automatique (INRIA).                               *)
(*                                                                        *)
(*  All files except ocaml-lib/pmap.{ml,mli} and ocaml-libpset.{ml,mli}   *)
(*  are distributed under the license below.  The former are distributed  *)
(*  under the LGPLv2, as in the LICENSE file.                             *)
(*                                                                        *)
(*                                                                        *)
(*  Redistribution and use in source and binary forms, with or without    *)
(*  modification, are permitted provided that the following conditions    *)
(*  are met:                                                              *)
(*  1. Redistributions of source code must retain the above copyright     *)
(*  notice, this list of conditions and the following disclaimer.         *)
(*  2. Redistributions in binary form must reproduce the above copyright  *)
(*  notice, this list of conditions and the following disclaimer in the   *)
(*  documentation and/or other materials provided with the distribution.  *)
(*  3. The names of the authors may not be used to endorse or promote     *)
(*  products derived from this software without specific prior written    *)
(*  permission.                                                           *)
(*                                                                        *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHORS ``AS IS'' AND ANY EXPRESS    *)
(*  OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED     *)
(*  WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE    *)
(*  ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY       *)
(*  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL    *)
(*  DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE     *)
(*  GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS         *)
(*  INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER  *)
(*  IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR       *)
(*  OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN   *)
(*  IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                         *)
(*========================================================================*)

chapter \<open>Auxiliary Definitions needed by Lem\<close>

theory "LemExtraDefs"

imports
   Main
   "HOL-Library.Permutation"
   "HOL-Library.While_Combinator"
begin

subsection \<open>General\<close>

consts failwith :: " 'a \<Rightarrow> 'b"

subsection \<open>Lists\<close>

fun index :: " 'a list \<Rightarrow> nat \<Rightarrow> 'a option "  where
   "index [] n = None"
 | "index (x # xs) 0 = Some x"
 | "index (x # xs) (Suc n) = index xs n"

lemma index_eq_some [simp]:
   "index l n = Some x \<longleftrightarrow> (n < length l \<and> (x = l ! n))"
proof (induct l arbitrary: n x)
  case Nil thus ?case by simp
next
  case (Cons e es n x)
  note ind_hyp = this

  show ?case
  proof (cases n)
    case 0 thus ?thesis by auto
  next
    case (Suc n')
    with ind_hyp show ?thesis by simp
  qed
qed

lemma index_eq_none [simp]:
   "index l n = None \<longleftrightarrow> length l \<le> n"
by (rule iffD1[OF Not_eq_iff]) auto


lemma index_simps [simp]:
   "length l \<le> n \<Longrightarrow> index l n = None"
   "n < length l \<Longrightarrow> index l n = Some (l ! n)"
by (simp_all)

fun find_indices :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat list" where
   "find_indices P [] = []"
 | "find_indices P (x # xs) = (if P x then 0 # (map Suc (find_indices P xs)) else (map Suc (find_indices P xs)))"

lemma length_find_indices :
  "length (find_indices P l) \<le> length l"
by (induct l) auto

lemma sorted_map_suc :
  "sorted l \<Longrightarrow> sorted (map Suc l)"
by (induct l) (simp_all)

lemma sorted_find_indices :
  "sorted (find_indices P xs)"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  from sorted_map_suc[OF this]
  show ?case
    by (simp)
qed

lemma find_indices_set [simp] :
  "set (find_indices P l) = {i. i < length l \<and> P (l ! i)}"
proof (intro set_eqI)
  fix i
  show "i \<in> set (find_indices P l) \<longleftrightarrow> (i \<in> {i. i < length l \<and> P (l ! i)})"
  proof (induct l arbitrary: i)
    case Nil thus ?case by simp
  next
    case (Cons x l' i)
    note ind_hyp = this
    show ?case
    proof (cases i)
      case 0 thus ?thesis by auto
    next
      case (Suc i') with ind_hyp[of i'] show ?thesis by auto
    qed
  qed
qed

definition find_index where
  "find_index P xs = (case find_indices P xs of
      []    \<Rightarrow> None
    | i # _ \<Rightarrow> Some i)"

lemma find_index_eq_some [simp] :
  "(find_index P xs = Some ii) \<longleftrightarrow> (ii < length xs \<and> P (xs ! ii) \<and> (\<forall>i' < ii. \<not>(P (xs ! i'))))"
  (is "?lhs = ?rhs")
proof (cases "find_indices P xs")
  case Nil
  with find_indices_set[of P xs]
  show ?thesis
    unfolding find_index_def by auto
next
  case (Cons i il) note find_indices_eq = this

  from sorted_find_indices[of P xs] find_indices_eq
  have "sorted (i # il)" by simp
  hence i_leq: "\<And>i'. i' \<in> set (i # il) \<Longrightarrow> i \<le> i'" by auto

  from find_indices_set[of P xs, unfolded find_indices_eq]
  have set_i_il_eq:"\<And>i'. i' \<in> set (i # il) = (i' < length xs \<and> P (xs ! i'))"
    by simp

  have lhs_eq: "find_index P xs = Some i"
    unfolding find_index_def find_indices_eq by simp

  show ?thesis
  proof (intro iffI)
    assume ?lhs
    with lhs_eq have ii_eq[simp]: "ii = i" by simp

    from set_i_il_eq[of i] i_leq[unfolded set_i_il_eq]
    show ?rhs by auto (metis leD less_trans)
  next
    assume ?rhs
    with set_i_il_eq[of ii]
    have "ii \<in> set (i # il) \<and> (ii \<le> i)"
      by (metis leI length_pos_if_in_set nth_Cons_0 nth_mem set_i_il_eq)

    with i_leq [of ii] have "i = ii" by simp
    thus ?lhs unfolding lhs_eq by simp
  qed
qed

lemma find_index_eq_none [simp] :
  "(find_index P xs = None) \<longleftrightarrow> (\<forall>x \<in> set xs. \<not>(P x))" (is "?lhs = ?rhs")
proof (rule iffD1[OF Not_eq_iff], intro iffI)
  assume "\<not> ?lhs"
  then obtain i where "find_index P xs = Some i" by auto
  hence "i < length xs \<and> P (xs ! i)" by simp
  thus "\<not> ?rhs" by auto
next
  let ?p = "(\<lambda>i. i < length xs \<and> P(xs ! i))"

  assume "\<not> ?rhs"
  then obtain i where "?p i"
    by (metis in_set_conv_nth)

  from LeastI [of ?p, OF \<open>?p i\<close>]
  have "?p (Least ?p)" .

  hence "find_index P xs = Some (Least ?p)"
    by (subst find_index_eq_some) (metis (mono_tags) less_trans not_less_Least)

  thus "\<not> ?lhs" by blast
qed

definition genlist where
  "genlist f n = map f (upt 0 n)"

lemma genlist_length [simp] :
  "length (genlist f n) = n"
unfolding genlist_def by simp

lemma genlist_simps [simp]:
   "genlist f 0 = []"
   "genlist f (Suc n) = genlist f n @ [f n]"
unfolding genlist_def by auto

definition split_at where
  "split_at n l = (take n l, drop n l)"

fun delete_first :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list) option "  where
    "delete_first P [] = None"
  | "delete_first P (x # xs) =
     (if (P x) then Some xs else
      map_option (\<lambda>xs'. x # xs') (delete_first P xs))"
declare delete_first.simps [simp del]

lemma delete_first_simps [simp] :
   "delete_first P [] = None"
   "P x \<Longrightarrow> delete_first P (x # xs) = Some xs"
   "\<not>(P x) \<Longrightarrow> delete_first P (x # xs) = map_option (\<lambda>xs'. x # xs') (delete_first P xs)"
unfolding delete_first.simps by auto

lemmas delete_first_unroll = delete_first.simps(2)


lemma delete_first_eq_none [simp] :
  "delete_first P l = None \<longleftrightarrow> (\<forall>x \<in> set l. \<not> (P x))"
by (induct l) (auto simp add: delete_first_unroll)

lemma delete_first_eq_some :
  "delete_first P l = (Some l') \<longleftrightarrow> (\<exists>l1 x l2. P x \<and> (\<forall>x \<in> set l1. \<not>(P x)) \<and> (l = l1 @ (x # l2)) \<and> (l' = l1 @ l2))"
  (is "?lhs l l' = (\<exists>l1 x l2. ?rhs_body l1 x l2 l l')")
proof (induct l arbitrary: l')
  case Nil thus ?case by simp
next
  case (Cons e l l')
  note ind_hyp = this

  show ?case
  proof (cases "P e")
    case True
    show ?thesis
    proof (rule iffI)
      assume "?lhs (e # l) l'"
      with \<open>P e\<close> have "l = l'" by simp
      with \<open>P e\<close> have "?rhs_body [] e l' (e # l) l'" by simp
      thus "\<exists>l1 x l2. ?rhs_body l1 x l2 (e # l) l'" by blast
    next
      assume "\<exists>l1 x l2. ?rhs_body l1 x l2 (e # l) l'"
      then obtain l1 x l2 where body_ok: "?rhs_body l1 x l2 (e # l) l'" by blast

      from body_ok \<open>P e\<close> have l1_eq[simp]: "l = l'"
        by (cases l1) (simp_all)
      with \<open>P e\<close> show "?lhs (e # l) l'" by simp
    qed
  next
    case False
    define rhs_pred where "rhs_pred \<equiv> \<lambda>l1 x l2 l l'. ?rhs_body l1 x l2 l l'"
    have rhs_fold: "\<And>l1 x l2 l l'. ?rhs_body l1 x l2 l l' = rhs_pred l1 x l2 l l'"
       unfolding rhs_pred_def by simp

    have "(\<exists>z l1 x l2. rhs_pred l1 x l2 l z \<and> e # z = l') = (\<exists>l1 x l2. rhs_pred l1 x l2 (e # l) l')"
    proof (intro iffI)
      assume "\<exists>z l1 x l2. rhs_pred l1 x l2 l z \<and> e # z = l'"
      then obtain z l1 x l2 where "rhs_pred l1 x l2 l z" and l'_eq: "l' = e # z" by auto
      with \<open>\<not>(P e)\<close> have "rhs_pred (e # l1) x l2 (e # l) l'"
        unfolding rhs_pred_def by simp
      thus "\<exists>l1 x l2. rhs_pred l1 x l2 (e # l) l'" by blast
    next
      assume "\<exists>l1 x l2. rhs_pred l1 x l2 (e # l) l'"
      then obtain l1 x l2 where "rhs_pred l1 x l2 (e # l) l'" by blast
      with \<open>\<not> (P e)\<close> obtain l1' where l1_eq[simp]: "l1 = e # l1'"
        unfolding rhs_pred_def by (cases l1) (auto)

      with \<open>rhs_pred l1 x l2 (e # l) l'\<close>
      have "rhs_pred l1' x l2 l (l1' @ l2) \<and> e # (l1' @ l2) = l'"
        unfolding rhs_pred_def by (simp)
      thus "\<exists>z l1 x l2. rhs_pred l1 x l2 l z \<and> e # z = l'" by blast
    qed
    with \<open>\<not> P e\<close> show ?thesis
      unfolding rhs_fold
      by (simp add: ind_hyp[unfolded rhs_fold])
  qed
qed


lemma perm_eval [code] :
  "perm [] l \<longleftrightarrow> l = []" (is ?g1)
  "perm (x # xs) l \<longleftrightarrow> (case delete_first (\<lambda>e. e = x) l of
       None => False
     | Some l' => perm xs l')" (is ?g2)
proof -
  show ?g1 by auto
next
  show ?g2
  proof (cases "delete_first (\<lambda>e. e = x) l")
    case None note del_eq = this
    hence "x \<notin> set l" by auto
    with perm_set_eq [of "x # xs" l]
    have "\<not> perm (x # xs) l" by auto
    thus ?thesis unfolding del_eq by simp
  next
    case (Some l') note del_eq = this

    from del_eq[unfolded delete_first_eq_some]
    obtain l1 l2 where l_eq: "l = l1 @ [x] @ l2" and l'_eq: "l' = l1 @ l2" by auto

    have "(x # xs <~~> l1 @ x # l2) = (xs <~~> l1 @ l2)"
    proof -
      from perm_append_swap [of l1 "[x]"]
           perm_append2 [of "l1 @ [x]" "x # l1" l2]
      have "l1 @ x # l2 <~~> x # (l1 @ l2)" by simp
      hence "x # xs <~~> l1 @ x # l2 \<longleftrightarrow> x # xs <~~> x # (l1 @ l2)"
        by (metis perm.trans perm_sym)
      thus ?thesis by simp
    qed
    with del_eq l_eq l'_eq show ?thesis by simp
  qed
qed


fun sorted_by  :: "('a \<Rightarrow> 'a \<Rightarrow> bool)\<Rightarrow> 'a list \<Rightarrow> bool "  where
   "sorted_by cmp [] = True"
 | "sorted_by cmp [_] = True"
 | "sorted_by cmp (x1 # x2 # xs) = ((cmp x1 x2) \<and> sorted_by cmp (x2 # xs))"

lemma sorted_by_lesseq [simp] :
  "sorted_by ((\<le>) :: ('a::{linorder}) => 'a => bool) = sorted"
proof (rule ext)
  fix l :: "'a list"
  show "sorted_by (\<le>) l = sorted l"
  proof (induct l)
    case Nil thus ?case by simp
  next
    case (Cons x xs)
    thus ?case by (cases xs) (simp_all del: sorted.simps(2) add: sorted2_simps)
  qed
qed

lemma sorted_by_cons_imp :
  "sorted_by cmp (x # xs) \<Longrightarrow> sorted_by cmp xs"
by (cases xs) simp_all

lemma sorted_by_cons_trans :
  assumes trans_cmp: "transp cmp"
  shows "sorted_by cmp (x # xs) = ((\<forall>x' \<in> set xs . cmp x x') \<and> sorted_by cmp xs)"
proof (induct xs arbitrary: x)
  case Nil thus ?case by simp
next
  case (Cons x2 xs x1)
  note ind_hyp = this

  from trans_cmp
  show ?case
    by (auto simp add: ind_hyp transp_def)
qed


fun insert_sort_insert_by  :: "('a \<Rightarrow> 'a \<Rightarrow> bool)\<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list "  where
  "insert_sort_insert_by cmp e ([]) = ( [e])"
| "insert_sort_insert_by cmp e (x # xs) = ( if cmp e x then (e # (x # xs)) else x # (insert_sort_insert_by cmp e xs))"


lemma insert_sort_insert_by_length [simp] :
  "length (insert_sort_insert_by cmp e l) = Suc (length l)"
by (induct l) auto

lemma insert_sort_insert_by_set [simp] :
  "set (insert_sort_insert_by cmp e l) = insert e (set l)"
by (induct l) auto

lemma insert_sort_insert_by_perm :
  "(insert_sort_insert_by cmp e l) <~~> (e # l)"
proof (induct l)
  case Nil thus ?case by simp
next
  case (Cons e2 l')
  note ind_hyp = this

  have "e2 # e # l' <~~> e # e2 # l'" by (rule perm.swap)
  hence "e2 # insert_sort_insert_by cmp e l' <~~> e # e2 # l'"
    using ind_hyp by (metis cons_perm_eq perm.trans)
  thus ?case by simp
qed


lemma insert_sort_insert_by_sorted_by :
assumes cmp_cases: "\<And>y. y \<in> set l \<Longrightarrow> \<not> (cmp e y) \<Longrightarrow> cmp y e"
assumes cmp_trans: "transp cmp"
shows "sorted_by cmp l \<Longrightarrow> sorted_by cmp (insert_sort_insert_by cmp e l)"
using cmp_cases
proof (induct l)
  case Nil thus ?case by simp
next
  case (Cons x1 l')
  note ind_hyp = Cons(1)
  note sorted_x1_l' = Cons(2)
  note cmp_cases = Cons(3)

  show ?case
  proof (cases l')
    case Nil with cmp_cases show ?thesis by simp
  next
    case (Cons x2 l'') note l'_eq = this

    from l'_eq sorted_x1_l' have "cmp x1 x2" "sorted_by cmp l'" by simp_all

    show ?thesis
    proof (cases "cmp e x1")
      case True
      with \<open>cmp x1 x2\<close> \<open>sorted_by cmp l'\<close>
      have "sorted_by cmp (x1 # l')"
        unfolding l'_eq by (simp)
      with \<open>cmp e x1\<close>
      show ?thesis by simp
    next
      case False

      with cmp_cases have "cmp x1 e" by simp
      have "\<And>x'.  x' \<in> set l' \<Longrightarrow> cmp x1 x'"
      proof -
        fix x'
        assume "x' \<in> set l'"
        hence "x' = x2 \<or> cmp x2 x'"
          using \<open>sorted_by cmp l'\<close> l'_eq sorted_by_cons_trans [OF cmp_trans, of x2 l'']
          by auto
        with transpD[OF cmp_trans, of x1 x2 x'] \<open>cmp x1 x2\<close>
        show "cmp x1 x'" by blast
      qed
      hence "sorted_by cmp (x1 # insert_sort_insert_by cmp e l')"
        using ind_hyp [OF \<open>sorted_by cmp l'\<close>] \<open>cmp x1 e\<close> cmp_cases
        unfolding sorted_by_cons_trans[OF cmp_trans]
        by simp
      with \<open>\<not>(cmp e x1)\<close>
      show ?thesis by simp
    qed
  qed
qed



fun insert_sort_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list "  where
    "insert_sort_by cmp [] = []"
  | "insert_sort_by cmp (x # xs) = insert_sort_insert_by cmp x (insert_sort_by cmp xs)"


lemma insert_sort_by_perm :
  "(insert_sort_by cmp l) <~~> l"
proof (induct l)
  case Nil thus ?case by simp
next
  case (Cons x l)
  thus ?case
   by simp (metis cons_perm_eq insert_sort_insert_by_perm perm.trans)
qed

lemma insert_sort_by_length [simp]:
  "length (insert_sort_by cmp l) = length l"
by (induct l) auto

lemma insert_sort_by_set [simp]:
  "set (insert_sort_by cmp l) = set l"
by (induct l) auto

definition sort_by where
  "sort_by = insert_sort_by"

lemma sort_by_simps [simp]:
  "length (sort_by cmp l) = length l"
  "set (sort_by cmp l) = set l"
unfolding sort_by_def by simp_all

lemma sort_by_perm :
  "sort_by cmp l <~~> l"
unfolding sort_by_def
by (simp add: insert_sort_by_perm)

subsection \<open>Maps\<close>

definition map_image :: "('v \<Rightarrow> 'w) \<Rightarrow> ('k, 'v) map \<Rightarrow> ('k, 'w) map" where
  "map_image f m = (\<lambda>k. map_option f (m k))"

definition map_domain_image :: "('k \<Rightarrow> 'v \<Rightarrow> 'w) \<Rightarrow> ('k, 'v) map \<Rightarrow> ('k, 'w) map" where
  "map_domain_image f m = (\<lambda>k. map_option (f k) (m k))"


lemma map_image_simps [simp]:
  "(map_image f m) k = None \<longleftrightarrow> m k = None"
  "(map_image f m) k = Some x \<longleftrightarrow> (\<exists>x'. (m k = Some x') \<and> (x = f x'))"
  "(map_image f Map.empty) = Map.empty"
  "(map_image f (m (k \<mapsto> v)) = (map_image f m) (k \<mapsto> f v))"
unfolding map_image_def by auto

lemma map_image_dom_ran [simp]:
  "dom (map_image f m) = dom m"
  "ran (map_image f m) = f ` (ran m)"
unfolding dom_def ran_def by auto

definition map_to_set :: "('k, 'v) map \<Rightarrow> ('k * 'v) set" where
  "map_to_set m = { (k, v) . m k = Some v }"

lemma map_to_set_simps [simp] :
  "map_to_set Map.empty = {}"  (is ?g1)
  "map_to_set (m ((k::'k) \<mapsto> (v::'v))) = (insert (k, v) (map_to_set (m |` (- {k}))))" (is ?g2)
proof -
  show ?g1 unfolding map_to_set_def by simp
next
  show ?g2
  proof (rule set_eqI)
    fix kv :: "('k * 'v)"
    obtain k' v' where kv_eq[simp]: "kv = (k', v')" by (rule prod.exhaust)

    show "(kv \<in> map_to_set (m(k \<mapsto> v))) = (kv \<in> insert (k, v) (map_to_set (m |` (- {k}))))"
      by (auto simp add: map_to_set_def)
  qed
qed


subsection \<open>Sets\<close>

definition "set_choose s \<equiv> (SOME x. (x \<in> s))"
  
definition without_trans_edges :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" where
  "without_trans_edges S \<equiv>
     let ts = trancl S in
       { (x, y) \<in> S. \<forall>z \<in> snd ` S. x \<noteq> z \<and> y \<noteq> z \<longrightarrow> \<not> ((x, z) \<in> ts \<and> (z, y) \<in> ts)}"
  
definition unbounded_lfp :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "unbounded_lfp S f \<equiv>
     while (\<lambda>x. x \<subset> S) f S"
  
definition unbounded_gfp :: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "unbounded_gfp S f \<equiv>
     while (\<lambda>x. S \<subset> x) f S"

lemma set_choose_thm[simp]:
  "s \<noteq> {} \<Longrightarrow> (set_choose s) \<in> s"
unfolding set_choose_def
by (rule someI_ex) auto

lemma set_choose_sing [simp]:
  "set_choose {x} = x"
  unfolding set_choose_def
  by auto

lemma set_choose_code [code]:
  "set_choose (set [x]) = x"
by auto

lemma set_choose_in [intro] :
  assumes "s \<noteq> {}"
  shows "set_choose s \<in> s"
proof -
  from \<open>s \<noteq> {}\<close>
  obtain x where "x \<in> s" by auto
  thus ?thesis
    unfolding set_choose_def
    by (rule someI)
qed


definition set_case where
  "set_case s c_empty c_sing c_else =
    (if (s = {}) then c_empty else
    (if (card s = 1) then c_sing (set_choose s) else
       c_else))"

lemma set_case_simps [simp] :
  "set_case {} c_empty c_sing c_else = c_empty"
  "set_case {x} c_empty c_sing c_else = c_sing x"
  "card s > 1 \<Longrightarrow> set_case s c_empty c_sing c_else = c_else"
  "\<not>(finite s) \<Longrightarrow> set_case s c_empty c_sing c_else = c_else"
unfolding set_case_def by auto

lemma set_case_simp_insert2 [simp] :
assumes x12_neq: "x1 \<noteq> x2"
shows "set_case (insert x1 (insert x2 xs))  c_empty c_sing c_else = c_else"
proof (cases "finite xs")
  case False thus ?thesis by (simp)
next
  case True note fin_xs = this

  have "card {x1,x2} \<le> card (insert x1 (insert x2 xs))"
    by (rule card_mono) (auto simp add: fin_xs)
  with x12_neq have "1 < card (insert x1 (insert x2 xs))" by simp
  thus ?thesis by auto
qed

lemma set_case_code [code] :
  "set_case (set []) c_empty c_sing c_else = c_empty"
  "set_case (set [x]) c_empty c_sing c_else = c_sing x"
  "set_case (set (x1 # x2 # xs)) c_empty c_sing c_else =
   (if (x1 = x2) then
     set_case (set (x2 # xs)) c_empty c_sing c_else
   else
     c_else)"
by auto

definition set_lfp:: "'a set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "set_lfp s f = lfp (\<lambda>s'. f s' \<union> s)"

lemma set_lfp_tail_rec_def :
assumes mono_f: "mono f"
shows "set_lfp s f = (if (f s) \<subseteq> s then s else (set_lfp (s \<union> f s) f))" (is "?ls = ?rs")
proof (cases "f s \<subseteq> s")
  case True note fs_sub_s = this

  from fs_sub_s have "\<Inter>{u. f u \<union> s \<subseteq> u} = s" by auto
  hence "?ls = s" unfolding set_lfp_def lfp_def .
  with fs_sub_s show "?ls = ?rs" by simp
next
  case False note not_fs_sub_s = this

  from mono_f have mono_f': "mono (\<lambda>s'. f s' \<union> s)"
    unfolding mono_def by auto

  have "\<Inter>{u. f u \<union> s \<subseteq> u} = \<Inter>{u. f u \<union> (s \<union> f s) \<subseteq> u}" (is "\<Inter>?S1 = \<Inter>?S2")
  proof
    have "?S2 \<subseteq> ?S1" by auto
    thus "\<Inter>?S1 \<subseteq> \<Inter>?S2" by (rule Inf_superset_mono)
  next
    { fix e
      assume "e \<in> \<Inter>?S2"
      hence S2_prop: "\<And>s'. f s' \<subseteq> s' \<Longrightarrow> s \<subseteq> s' \<Longrightarrow> f s \<subseteq> s' \<Longrightarrow> e \<in> s'" by simp

      { fix s'
        assume "f s' \<subseteq> s'" "s \<subseteq> s'"

        from mono_f \<open>s \<subseteq> s'\<close>
        have "f s \<subseteq> f s'" unfolding mono_def by simp
        with \<open>f s' \<subseteq> s'\<close> have "f s \<subseteq> s'" by simp
        with \<open>f s' \<subseteq> s'\<close> \<open>s \<subseteq> s'\<close> S2_prop
        have "e \<in> s'" by simp
      }
      hence "e \<in> \<Inter>?S1" by simp
    }
    thus "\<Inter>?S2 \<subseteq> \<Inter>?S1" by auto
  qed
  hence "?ls = (set_lfp (s \<union> f s) f)"
     unfolding set_lfp_def lfp_def .
  with not_fs_sub_s show "?ls = ?rs" by simp
qed

lemma set_lfp_simps [simp] :
"mono f \<Longrightarrow> f s \<subseteq> s \<Longrightarrow> set_lfp s f = s"
"mono f \<Longrightarrow> \<not>(f s \<subseteq> s) \<Longrightarrow> set_lfp s f = (set_lfp (s \<union> f s) f)"
by (metis set_lfp_tail_rec_def)+


fun insert_in_list_at_arbitrary_pos where
   "insert_in_list_at_arbitrary_pos x [] = {[x]}"
 | "insert_in_list_at_arbitrary_pos x (y # ys) =
    insert (x # y # ys) ((\<lambda>l. y # l) ` (insert_in_list_at_arbitrary_pos x ys))"

lemma insert_in_list_at_arbitrary_pos_thm :
  "xl \<in> insert_in_list_at_arbitrary_pos x l \<longleftrightarrow>
   (\<exists>l1 l2. l = l1 @ l2 \<and> xl = l1 @ [x] @ l2)"
proof (induct l arbitrary: xl)
  case Nil thus ?case by simp
next
  case (Cons y l xyl)
  note ind_hyp = this

  show ?case
  proof (rule iffI)
    assume xyl_in: "xyl \<in> insert_in_list_at_arbitrary_pos x (y # l)"
    show "\<exists>l1 l2. y # l = l1 @ l2 \<and> xyl = l1 @ [x] @ l2"
    proof (cases "xyl = x # y # l")
      case True
      hence "y # l = [] @ (y # l) \<and> xyl = [] @ [x] @ (y # l)" by simp
      thus ?thesis by blast
    next
      case False
      with xyl_in have "xyl \<in> (#) y ` insert_in_list_at_arbitrary_pos x l" by simp
      with ind_hyp obtain l1 l2 where "l = l1 @ l2 \<and> xyl = y # l1 @ x # l2"
         by (auto simp add: image_def Bex_def)
      hence "y # l = (y # l1) @ l2 \<and> xyl = (y # l1) @ [x] @ l2" by simp
      thus ?thesis by blast
    qed
  next
    assume "\<exists>l1 l2. y # l = l1 @ l2 \<and> xyl = l1 @ [x] @ l2"
    then obtain l1 l2 where yl_eq: "y # l = l1 @ l2" and xyl_eq: "xyl = l1 @ [x] @ l2" by blast
    show "xyl \<in> insert_in_list_at_arbitrary_pos x (y # l)"
    proof (cases l1)
      case Nil
      with yl_eq xyl_eq
      have "xyl = x # y # l" by simp
      thus ?thesis by simp
    next
      case (Cons y' l1')
      with yl_eq have l1_eq: "l1 = y # l1'" and l_eq: "l = l1' @ l2" by simp_all

      have "\<exists>l1'' l2''. l = l1'' @ l2'' \<and> l1' @ [x] @ l2 = l1'' @ [x] @ l2''"
        apply (rule_tac exI[where x = l1'])
        apply (rule_tac exI [where x = l2])
        apply (simp add: l_eq)
      done
      hence "(l1' @ [x] @ l2) \<in> insert_in_list_at_arbitrary_pos x l"
        unfolding ind_hyp by blast
      hence "\<exists>l'. l' \<in> insert_in_list_at_arbitrary_pos x l \<and> l1 @ x # l2 = y # l'"
        by (rule_tac exI [where x = "l1' @ [x] @ l2"]) (simp add: l1_eq)
      thus ?thesis
        by (simp add: image_def Bex_def xyl_eq)
    qed
  qed
qed

definition list_of_set_set :: "'a set \<Rightarrow> ('a list) set" where
"list_of_set_set s = { l . (set l = s) \<and> distinct l }"

lemma list_of_set_set_empty [simp]:
  "list_of_set_set {} = {[]}"
unfolding list_of_set_set_def by auto

lemma list_of_set_set_insert [simp] :
  "list_of_set_set (insert x s) =
     \<Union> ((insert_in_list_at_arbitrary_pos x) ` (list_of_set_set (s - {x})))"
   (is "?lhs = ?rhs")
proof (intro set_eqI)
  fix l

  have "(set l = insert x s \<and> distinct l) \<longleftrightarrow> (\<exists>l1 l2. set (l1 @ l2) = s - {x} \<and> distinct (l1 @ l2) \<and> l = l1 @ x # l2)"
  proof (intro iffI)
    assume "set l = insert x s \<and> distinct l"
    hence set_l_eq: "set l = insert x s" and "distinct l" by simp_all

    from \<open>set l = insert x s\<close>
    have "x \<in> set l" by simp
    then obtain l1 l2 where l_eq: "l = l1 @ x # l2"
      unfolding in_set_conv_decomp by blast

    from \<open>distinct l\<close>  l_eq
    have "distinct (l1 @ l2)" and x_nin: "x \<notin> set (l1 @ l2)"
      by auto

    from x_nin set_l_eq[unfolded l_eq]
    have set_l12_eq: "set (l1 @ l2) = s - {x}"
      by auto

    from \<open>distinct (l1 @ l2)\<close> l_eq set_l12_eq
    show "\<exists>l1 l2. set (l1 @ l2) = s - {x} \<and> distinct (l1 @ l2) \<and> l = l1 @ x # l2"
      by blast
  next
    assume "\<exists>l1 l2. set (l1 @ l2) = s - {x} \<and> distinct (l1 @ l2) \<and> l = l1 @ x # l2"
    then obtain l1 l2 where "set (l1 @ l2) = s - {x}"  "distinct (l1 @ l2)" "l = l1 @ x # l2"
      by blast
    thus "set l = insert x s \<and> distinct l"
       by auto
  qed

  thus "l \<in> list_of_set_set (insert x s) \<longleftrightarrow> l \<in> (\<Union> ((insert_in_list_at_arbitrary_pos x) ` (list_of_set_set (s - {x}))))"
     unfolding list_of_set_set_def
     by (simp add: insert_in_list_at_arbitrary_pos_thm ex_simps[symmetric] del: ex_simps)
qed

lemma list_of_set_set_code [code]:
  "list_of_set_set (set []) = {[]}"
  "list_of_set_set (set (x # xs)) =
     \<Union> ((insert_in_list_at_arbitrary_pos x) ` (list_of_set_set ((set xs) - {x})))"
by simp_all

lemma list_of_set_set_is_empty :
  "list_of_set_set s = {} \<longleftrightarrow> \<not> (finite s)"
proof -
  have "finite s \<longleftrightarrow> (\<exists>l. set l = s \<and> distinct l)"
  proof (rule iffI)
    assume "\<exists>l. set l = s \<and> distinct l" then
    obtain l where "s = set l" by blast
    thus "finite s" by simp
  next
    assume "finite s"
    thus "\<exists>l. set l = s \<and> distinct l"
    proof (induct s)
      case empty
      show ?case by auto
    next
      case (insert e s)
      note e_nin_s = insert(2)
      from insert(3) obtain l where set_l: "set l = s" and dist_l: "distinct l" by blast

      from set_l have set_el: "set (e # l) = insert e s" by auto
      from dist_l set_l e_nin_s have dist_el: "distinct (e # l)" by simp

      from set_el dist_el show ?case by blast
    qed
  qed
  thus ?thesis
    unfolding list_of_set_set_def by simp
qed

definition list_of_set :: "'a set \<Rightarrow> 'a list" where
   "list_of_set s = set_choose (list_of_set_set s)"

lemma list_of_set [simp] :
  assumes fin_s: "finite s"
  shows "set (list_of_set s) = s"
        "distinct (list_of_set s)"
proof -
  from fin_s list_of_set_set_is_empty[of s]
  have "\<not> (list_of_set_set s = {})" by simp
  hence "list_of_set s \<in> list_of_set_set s"
    unfolding list_of_set_def
    by (rule set_choose_thm)
  thus "set (list_of_set s) = s"
       "distinct (list_of_set s)" unfolding list_of_set_set_def
  by simp_all
qed

lemma list_of_set_in:
  "finite s \<Longrightarrow> list_of_set s \<in> list_of_set_set s"
unfolding list_of_set_def
by (metis list_of_set_set_is_empty set_choose_thm)

definition ordered_list_of_set where
  "ordered_list_of_set cmp s = set_choose (sort_by cmp ` list_of_set_set s)"

subsection \<open>sum\<close>

find_consts "'a list => ('a list * _)"

fun sum_partition :: "('a + 'b) list \<Rightarrow> 'a list * 'b list"  where
  "sum_partition [] = ([], [])"
| "sum_partition ((Inl l) # lrs) =
     (let (ll, rl) = sum_partition lrs in
     (l # ll, rl))"
| "sum_partition ((Inr r) # lrs) =
     (let (ll, rl) = sum_partition lrs in
     (ll, r # rl))"

lemma sum_partition_length :
  "List.length lrs = List.length (fst (sum_partition lrs)) + List.length (snd (sum_partition lrs))"
proof (induct lrs)
  case Nil thus ?case by simp
next
  case (Cons lr lrs) thus ?case
    by (cases lr) (auto split: prod.split)
qed

subsection \<open>sorting\<close>

subsection \<open>Strings\<close>

declare String.literal.explode_inverse [simp]

subsection \<open>num to string conversions\<close>

definition nat_list_to_string :: "nat list \<Rightarrow> string" where
  "nat_list_to_string nl = map char_of nl"

definition is_digit where
  "is_digit (n::nat) = (n < 10)"

lemma is_digit_simps[simp] :
  "n < 10 \<Longrightarrow> is_digit n"
  "\<not>(n < 10) \<Longrightarrow> \<not>(is_digit n)"
unfolding is_digit_def by simp_all

lemma is_digit_expand :
  "is_digit n \<longleftrightarrow>
     (n = 0) \<or> (n = 1) \<or> (n = 2) \<or> (n = 3) \<or>  (n = 4) \<or>
     (n = 5) \<or> (n = 6) \<or> (n = 7) \<or> (n = 8) \<or>  (n = 9)"
unfolding is_digit_def by auto

lemmas is_digitE = is_digit_expand[THEN iffD1,elim_format]
lemmas is_digitI = is_digit_expand[THEN iffD2,rule_format]

definition is_digit_char where
  "is_digit_char c \<longleftrightarrow>
     (c = CHR ''0'') \<or> (c = CHR ''5'') \<or>
     (c = CHR ''1'') \<or> (c = CHR ''6'') \<or>
     (c = CHR ''2'') \<or> (c = CHR ''7'') \<or>
     (c = CHR ''3'') \<or> (c = CHR ''8'') \<or>
     (c = CHR ''4'') \<or> (c = CHR ''9'')"

lemma is_digit_char_simps[simp] :
  "is_digit_char (CHR ''0'')"
  "is_digit_char (CHR ''1'')"
  "is_digit_char (CHR ''2'')"
  "is_digit_char (CHR ''3'')"
  "is_digit_char (CHR ''4'')"
  "is_digit_char (CHR ''5'')"
  "is_digit_char (CHR ''6'')"
  "is_digit_char (CHR ''7'')"
  "is_digit_char (CHR ''8'')"
  "is_digit_char (CHR ''9'')"
unfolding is_digit_char_def by simp_all

lemmas is_digit_charE = is_digit_char_def[THEN iffD1,elim_format]
lemmas is_digit_charI = is_digit_char_def[THEN iffD2,rule_format]

definition digit_to_char :: "nat \<Rightarrow> char" where
  "digit_to_char n = (
     if n = 0 then CHR ''0''
     else if n = 1 then CHR ''1''
     else if n = 2 then CHR ''2''
     else if n = 3 then CHR ''3''
     else if n = 4 then CHR ''4''
     else if n = 5 then CHR ''5''
     else if n = 6 then CHR ''6''
     else if n = 7 then CHR ''7''
     else if n = 8 then CHR ''8''
     else if n = 9 then CHR ''9''
     else CHR ''X'')"

lemma digit_to_char_simps [simp]:
  "digit_to_char 0 = CHR ''0''"
  "digit_to_char (Suc 0) = CHR ''1''"
  "digit_to_char 2 = CHR ''2''"
  "digit_to_char 3 = CHR ''3''"
  "digit_to_char 4 = CHR ''4''"
  "digit_to_char 5 = CHR ''5''"
  "digit_to_char 6 = CHR ''6''"
  "digit_to_char 7 = CHR ''7''"
  "digit_to_char 8 = CHR ''8''"
  "digit_to_char 9 = CHR ''9''"
  "n > 9 \<Longrightarrow> digit_to_char n = CHR ''X''"
unfolding digit_to_char_def
by simp_all

definition char_to_digit :: "char \<Rightarrow> nat" where
  "char_to_digit c = (
     if c = CHR ''0'' then 0
     else if c = CHR ''1'' then 1
     else if c = CHR ''2'' then 2
     else if c = CHR ''3'' then 3
     else if c = CHR ''4'' then 4
     else if c = CHR ''5'' then 5
     else if c = CHR ''6'' then 6
     else if c = CHR ''7'' then 7
     else if c = CHR ''8'' then 8
     else if c = CHR ''9'' then 9
     else 10)"

lemma char_to_digit_simps [simp]:
  "char_to_digit (CHR ''0'') = 0"
  "char_to_digit (CHR ''1'') = 1"
  "char_to_digit (CHR ''2'') = 2"
  "char_to_digit (CHR ''3'') = 3"
  "char_to_digit (CHR ''4'') = 4"
  "char_to_digit (CHR ''5'') = 5"
  "char_to_digit (CHR ''6'') = 6"
  "char_to_digit (CHR ''7'') = 7"
  "char_to_digit (CHR ''8'') = 8"
  "char_to_digit (CHR ''9'') = 9"
unfolding char_to_digit_def by simp_all


lemma diget_to_char_inv[simp]:
assumes is_digit: "is_digit n"
shows "char_to_digit (digit_to_char n) = n"
using is_digit unfolding is_digit_expand by auto

lemma char_to_diget_inv[simp]:
assumes is_digit: "is_digit_char c"
shows "digit_to_char (char_to_digit c) = c"
using is_digit
unfolding char_to_digit_def is_digit_char_def
by auto

lemma char_to_digit_div_mod [simp]:
assumes is_digit: "is_digit_char c"
shows "char_to_digit c < 10"
using is_digit
unfolding char_to_digit_def is_digit_char_def
by auto


lemma is_digit_char_intro[simp]:
  "is_digit (char_to_digit c) = is_digit_char c"
unfolding char_to_digit_def is_digit_char_def is_digit_expand
by auto

lemma is_digit_intro[simp]:
  "is_digit_char (digit_to_char n) = is_digit n"
unfolding digit_to_char_def is_digit_char_def is_digit_expand
by auto

lemma digit_to_char_11:
"digit_to_char n1 = digit_to_char n2 \<Longrightarrow>
 (is_digit n1 = is_digit n2) \<and> (is_digit n1 \<longrightarrow> (n1 = n2))"
by (metis diget_to_char_inv is_digit_intro)

lemma char_to_digit_11:
"char_to_digit c1 = char_to_digit c2 \<Longrightarrow>
 (is_digit_char c1 = is_digit_char c2) \<and> (is_digit_char c1 \<longrightarrow> (c1 = c2))"
by (metis char_to_diget_inv is_digit_char_intro)

function nat_to_string :: "nat \<Rightarrow> string" where
  "nat_to_string n =
     (if (is_digit n) then [digit_to_char n] else
      nat_to_string (n div 10) @ [digit_to_char (n mod 10)])"
by auto
termination
  by (relation "measure id") (auto simp add: is_digit_def)

definition int_to_string :: "int \<Rightarrow> string" where
  "int_to_string i \<equiv>
     if i < 0 then
       ''-'' @ nat_to_string (nat (abs i))
     else
       nat_to_string (nat i)"

lemma nat_to_string_simps[simp]:
   "is_digit n \<Longrightarrow> nat_to_string n = [digit_to_char n]"
  "\<not>(is_digit n) \<Longrightarrow> nat_to_string n = nat_to_string (n div 10) @ [digit_to_char (n mod 10)]"
by simp_all
declare nat_to_string.simps[simp del]

lemma nat_to_string_neq_nil[simp]:
  "nat_to_string n \<noteq> []"
  by (cases "is_digit n") simp_all

lemmas nat_to_string_neq_nil2[simp] = nat_to_string_neq_nil[symmetric]

lemma nat_to_string_char_to_digit [simp]:
  "is_digit_char c \<Longrightarrow> nat_to_string (char_to_digit c) = [c]"
by auto

lemma nat_to_string_11[simp] :
  "(nat_to_string n1 = nat_to_string n2) \<longleftrightarrow> n1 = n2"
proof (rule iffI)
  assume "n1 = n2"
  thus "nat_to_string n1 = nat_to_string n2" by simp
next
  assume "nat_to_string n1 = nat_to_string n2"
  thus "n1 = n2"
  proof (induct n2 arbitrary: n1 rule: less_induct)
    case (less n2')
    note ind_hyp = this(1)
    note n2s_eq = less(2)

    have is_dig_eq: "is_digit n2' = is_digit n1" using n2s_eq
      apply (cases "is_digit n2'")
      apply (case_tac [!] "is_digit n1")
      apply (simp_all)
    done

    show ?case
    proof (cases "is_digit n2'")
      case True with n2s_eq is_dig_eq show ?thesis by simp (metis digit_to_char_11)
    next
      case False
      with is_dig_eq have not_digs : "\<not> (is_digit n1)"  "\<not> (is_digit n2')" by simp_all

      from not_digs(2) have "n2' div 10 < n2'" unfolding is_digit_def by auto
      note ind_hyp' = ind_hyp [OF this, of "n1 div 10"]

      from not_digs n2s_eq ind_hyp' digit_to_char_11[of "n1 mod 10" "n2' mod 10"]
      have "(n1 mod 10) = (n2' mod 10)" "n1 div 10 = n2' div 10" by simp_all
      thus "n1 = n2'" by (metis div_mult_mod_eq)
    qed
  qed
qed

definition "is_nat_string s \<equiv> (\<forall>c\<in>set s. is_digit_char c)"
definition "is_strong_nat_string s \<equiv> is_nat_string s \<and> (s \<noteq> []) \<and> (hd s = CHR ''0'' \<longrightarrow> length s = 1)"

lemma is_nat_string_simps[simp]:
  "is_nat_string []"
  "is_nat_string (c # s) \<longleftrightarrow> is_digit_char c \<and> is_nat_string s"
unfolding is_nat_string_def by simp_all

lemma is_strong_nat_string_simps[simp]:
  "\<not>(is_strong_nat_string [])"
  "is_strong_nat_string (c # s) \<longleftrightarrow> is_digit_char c \<and> is_nat_string s \<and>
                                    (c = CHR ''0'' \<longrightarrow> s = [])"
unfolding is_strong_nat_string_def by simp_all

fun string_to_nat_aux :: "nat \<Rightarrow> string \<Rightarrow> nat" where
   "string_to_nat_aux n [] = n"
 | "string_to_nat_aux n (d#ds) =
    string_to_nat_aux (n*10 + char_to_digit d) ds"

definition string_to_nat :: "string \<Rightarrow> nat option" where
   "string_to_nat s \<equiv>
    (if is_nat_string s then Some (string_to_nat_aux 0 s) else None)"

definition string_to_nat' :: "string \<Rightarrow> nat" where
  "string_to_nat' s \<equiv> the (string_to_nat s)"

lemma string_to_nat_aux_inv :
assumes "is_nat_string s"
assumes "n > 0 \<or> is_strong_nat_string s"
shows "nat_to_string (string_to_nat_aux n s) =
(if n = 0 then '''' else nat_to_string n) @ s"
using assms
proof (induct s arbitrary: n)
  case Nil
  thus ?case
    by (simp add: is_strong_nat_string_def)
next
  case (Cons c s n)
  from Cons(2) have "is_digit_char c" "is_nat_string s" by simp_all
  note cs_ok = Cons(3)
  let ?m = "n*10 + char_to_digit c"
  note ind_hyp = Cons(1)[OF \<open>is_nat_string s\<close>, of ?m]

  from \<open>is_digit_char c\<close> have m_div: "?m div 10 = n" and
                              m_mod: "?m mod 10 = char_to_digit c"
    unfolding is_digit_char_def
    by auto

  show ?case
  proof (cases "?m = 0")
    case True
    with \<open>is_digit_char c\<close>
    have "n = 0" "c = CHR ''0''" unfolding is_digit_char_def by auto
    moreover with cs_ok have "s = []" by simp
    ultimately show ?thesis by simp
  next
    case False note m_neq_0 = this
    with ind_hyp have ind_hyp':
      "nat_to_string (string_to_nat_aux ?m s) = (nat_to_string ?m) @ s" by auto

    hence "nat_to_string (string_to_nat_aux n (c # s)) = (nat_to_string ?m) @ s"
      by simp

    with \<open>is_digit_char c\<close> m_div show ?thesis by simp
  qed
qed

lemma string_to_nat_inv :
assumes strong_nat_s: "is_strong_nat_string s"
assumes s2n_s: "string_to_nat s = Some n"
shows "nat_to_string n = s"
proof -
  from strong_nat_s have nat_s: "is_nat_string s" unfolding is_strong_nat_string_def by simp
  with s2n_s have n_eq: "n = string_to_nat_aux 0 s" unfolding string_to_nat_def by simp

  from string_to_nat_aux_inv[of s 0, folded n_eq] nat_s strong_nat_s
  show ?thesis by simp
qed

lemma nat_to_string_induct [case_names "digit" "non_digit"]:
assumes digit: "\<And>d. is_digit d \<Longrightarrow> P d"
assumes not_digit: "\<And>n. \<not>(is_digit n) \<Longrightarrow> P (n div 10) \<Longrightarrow> P (n mod 10) \<Longrightarrow> P n"
shows "P n"
proof (induct n rule: less_induct)
  case (less n)
  note ind_hyp = this

  show ?case
  proof (cases "is_digit n")
    case True with digit show ?thesis by simp
  next
    case False note not_dig = this
    hence "n div 10 < n" "n mod 10 < n" unfolding is_digit_def by auto
    with not_dig ind_hyp not_digit show ?thesis by simp
  qed
qed

lemma nat_to_string___is_nat_string [simp]:
  "is_nat_string (nat_to_string n)"
unfolding is_nat_string_def
proof (induct n rule: nat_to_string_induct)
  case (digit d)
  thus ?case by simp
next
  case (non_digit n)
  thus ?case by simp
qed

lemma nat_to_string___eq_0 [simp]:
  "(nat_to_string n = (CHR ''0'')#s) \<longleftrightarrow> (n = 0 \<and> s = [])"
unfolding is_nat_string_def
proof (induct n arbitrary: s rule: nat_to_string_induct)
  case (digit d) thus ?case unfolding is_digit_expand by auto
next
  case (non_digit n)

  obtain c s' where ns_eq: "nat_to_string (n div 10) = c # s'"
     by (cases "nat_to_string (n div 10)") auto

  from non_digit(1) have "n div 10 \<noteq> 0" unfolding is_digit_def by auto
  with non_digit(2) ns_eq have c_neq: "c \<noteq> CHR ''0''" by auto

  from \<open>\<not> (is_digit n)\<close> c_neq ns_eq
  show ?case by auto
qed

lemma nat_to_string___is_strong_nat_string:
  "is_strong_nat_string (nat_to_string n)"
proof (cases "is_digit n")
  case True thus ?thesis by simp
next
  case False note not_digit = this

  obtain c s' where ns_eq: "nat_to_string n = c # s'"
     by (cases "nat_to_string n") auto

  from not_digit have "0 < n" unfolding is_digit_def by simp
  with ns_eq have c_neq: "c \<noteq> CHR ''0''" by auto
  hence "hd (nat_to_string n) \<noteq> CHR ''0''" unfolding ns_eq by simp

  thus ?thesis unfolding is_strong_nat_string_def
    by simp
qed

lemma nat_to_string_inv :
  "string_to_nat (nat_to_string n) = Some n"
by (metis nat_to_string_11
          nat_to_string___is_nat_string
          nat_to_string___is_strong_nat_string
          string_to_nat_def
          string_to_nat_inv)

definition The_opt where
  "The_opt p = (if (\<exists>!x. p x) then Some (The p) else None)"

lemma The_opt_eq_some [simp] :
"((The_opt p) = (Some x)) \<longleftrightarrow> ((p x) \<and> ((\<forall> y.  p y \<longrightarrow> (x = y))))"
    (is "?lhs = ?rhs")
proof (cases "\<exists>!x. p x")
  case True
  note exists_unique = this
  then obtain x where p_x: "p x" by auto

  from the1_equality[of p x] exists_unique p_x
  have the_opt_eq: "The_opt p = Some x"
    unfolding The_opt_def by simp

  from exists_unique the_opt_eq p_x show ?thesis
    by auto
next
  case False
  note not_unique = this

  hence "The_opt p = None"
    unfolding The_opt_def by simp
  with not_unique show ?thesis by auto
qed

lemma The_opt_eq_none [simp] :
"((The_opt p) = None) \<longleftrightarrow> \<not>(\<exists>!x. p x)"
unfolding The_opt_def by auto


end
