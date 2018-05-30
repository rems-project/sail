open HolKernel boolLib bossLib Parse
open state_monadTheory
val _ = temp_tight_equality();

val _ = new_theory "state_monad_lemmas";

val () = monadsyntax.declare_monad("state_monad",
  { bind = ``bindS``,
    ignorebind = SOME ``seqS``,
    unit = ``returnS``,
    fail = SOME ``failS``,
    choice = SOME ``chooseS``,
    guard = SOME ``assert_expS`` });

val bindS_cases = Q.store_thm("bindS_cases",
  `(r, s') ∈ bindS m f s ⇒
   (∃a a' s''. r = Value a ∧ (Value a', s'') ∈ m s ∧ (Value a, s') ∈ f a' s'') ∨
   (∃e. r = Ex e ∧ (Ex e, s') ∈ m s) ∨
   (∃e a s''. r = Ex e ∧ (Value a, s'') ∈ m s ∧ (Ex e, s') ∈ f a s'')`,
  rw[bindS_def]
  \\ Cases_on`r` \\ fs[]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs[]
  \\ metis_tac[]);

val _ = export_theory();
