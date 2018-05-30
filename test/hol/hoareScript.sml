open HolKernel boolLib bossLib Parse pairTheory mp_then
open state_monadTheory state_monad_lemmasTheory

val _ = new_theory "hoare"

(* Hoare logic, as in the Isabelle version *)

val _ = type_abbrev("predS", ``:'regs sequential_state -> bool``);

val PrePost_def = Define`
  PrePost (P:'regs predS) (f:('regs, 'a, 'e)monadS) Q =
    ∀s. P s ⇒ (∀r. r ∈ f s ⇒ Q (FST r) (SND r))`;

val PrePostI = Q.store_thm("PrePostI",
  `(∀s r s'. P s ∧ (r,s') ∈ f s ⇒ Q r s') ⇒ PrePost P f Q`,
  rw[PrePost_def,FORALL_PROD] \\ res_tac);

val PrePost_elim = Q.store_thm("PrePost_elim",
  `PrePost P f Q ∧ P s ∧ (r, s') ∈ f s ⇒ Q r s'`,
  rw[PrePost_def] \\ res_tac \\ fs[]);

val PrePost_consequence = Q.store_thm("PrePost_consequence",
  `PrePost X f Y ∧ (∀s. P s ⇒ X s) ∧ (∀v s. Y v s ⇒ Q v s) ⇒ PrePost P f Q`,
  rw[PrePost_def] \\ ntac 3 res_tac);

val PrePost_strengthen_pre = Q.store_thm("PrePost_strengthen_pre",
  `PrePost X f Z ∧ (∀s. Y s ⇒ X s) ⇒ PrePost X f Z`,
  metis_tac[PrePost_consequence]);

val PrePost_weaken_post = Q.store_thm("PrePost_weaken_post",
  `PrePost X f Y ∧ (∀v s. Y v s ⇒ Z v s) ⇒ PrePost X f Z`,
  metis_tac[PrePost_consequence]);

val PrePost_True_post = Q.store_thm("PrePost_True_post[simp]",
  `PrePost P m (λ_ _. T)`, rw[PrePost_def]);

val PrePost_any = Q.store_thm("PrePost_any",
  `PrePost (λs. ∀r. r ∈ m s ⇒ Q (FST r) (SND r)) m Q`,
  rw[PrePost_def]);

val PrePost_returnS = Q.store_thm("PrePost_returnS",
  `PrePost (P (Value x)) (returnS x) P`,
  rw[PrePost_def, returnS_def]);

val PrePost_bindS = Q.store_thm("PrePost_bindS",
  `(∀s a s'. (Value a, s') ∈ m s ⇒ PrePost (R a) (f a) Q) ∧
   PrePost P m (λr. case r of Value a => R a | Ex e => Q (Ex e))
   ⇒
   PrePost P (bindS m f) Q`,
  strip_tac
  \\ match_mp_tac PrePostI
  \\ rw[]
  \\ drule (GEN_ALL PrePost_elim)
  \\ drule bindS_cases
  \\ rw[]
  \\ first_x_assum drule \\ strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ fs[]
  \\ match_mp_tac (GEN_ALL PrePost_elim)
  \\ metis_tac[]);

val PrePost_bindS_ignore = Q.store_thm("PrePost_bindS_ignore",
  `PrePost R f Q ∧ PrePost P m (λr. case r of Value a => R | Ex e => Q (Ex e)) ⇒
   PrePost P (bindS m (λ_. f)) Q`,
  strip_tac
  \\ match_mp_tac (GEN_ALL PrePost_bindS)
  \\ qexists_tac`λa. R` \\ simp[]);

val PrePost_seqS = save_thm("PrePost_seqS",
  PrePost_bindS_ignore
  |> INST_TYPE[delta |-> oneSyntax.one_ty]
  |> CONV_RULE(RAND_CONV(RATOR_CONV(RAND_CONV(REWR_CONV(GSYM seqS_def)))))
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> GEN_ALL);

val PrePost_bindS_unit = Q.store_thm("PrePost_bindS_unit",
  `PrePost R (f ()) Q ∧ PrePost P m (λr. case r of Value a => R | Ex e => Q (Ex e))
  ⇒ PrePost P (bindS m f) Q`,
  strip_tac
  \\ match_mp_tac (GEN_ALL PrePost_bindS)
  \\ qexists_tac`λa. R` \\ simp[]);

val PrePost_readS = Q.store_thm("PrePost_readS",
  `PrePost (λs. P (Value (f s)) s) (readS f) P`,
  rw[PrePost_def, readS_def, returnS_def]);

val PrePost_updateS = Q.store_thm("PrePost_updateS",
  `PrePost (λs. P (Value ()) (f s)) (updateS f) P`,
  rw[PrePost_def, updateS_def, returnS_def]);

val PrePostE_def = Define`
  PrePostE P f Q E = PrePost P f (λv. case v of Value a => Q a | Ex e => E e)`;

val _ = export_theory();

