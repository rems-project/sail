Require Import Sail.Values Sail.Prompt_monad Sail.Prompt Sail.State_monad Sail.State Sail.State Sail.State_lifting.
Require Import Sail.State_monad_lemmas.
Require Import Lia.

Local Open Scope equiv_scope.
Local Open Scope Z.

Lemma seqS_cong A RV E (m1 m1' : monadS RV unit E) (m2 m2' : monadS RV A E) :
  m1 === m1' ->
  m2 === m2' ->
  m1 >>$ m2 === m1' >>$ m2'.
unfold seqS.
auto using bindS_cong.
Qed.

Lemma foreachS_cong {A RV Vars E} xs vars f f' :
  (forall a vars, f a vars === f' a vars) ->
  @foreachS A RV Vars E xs vars f === foreachS xs vars f'.
intro H.
revert vars.
induction xs.
* reflexivity.
* intros. simpl.
  rewrite H.
  apply bindS_cong; auto.
Qed.

Add Parametric Morphism {Regs A Vars E : Type} : (@foreachS A Regs Vars E)
  with signature eq ==> eq ==> equiv ==> equiv as foreachS_morphism.
apply foreachS_cong.
Qed.

Lemma foreach_ZS_up_cong rv e Vars from to step vars body body' H :
  (forall a pf vars, body a pf vars === body' a pf vars) ->
  @foreach_ZS_up rv e Vars from to step vars body H === foreach_ZS_up from to step vars body'.
intro EQ.
unfold foreach_ZS_up.
match goal with
| |- @foreach_ZS_up' _ _ _ _ _ _ _ _ _ ?pf _ _ === _ => generalize pf
end.
generalize 0 at 2 3 4 as off.
revert vars.
induction (S (Z.abs_nat (from - to))); intros; simpl.
* reflexivity.
* destruct (sumbool_of_bool (from + off <=? to)); auto.
  rewrite EQ.
  setoid_rewrite IHn.
  reflexivity.
Qed.

Lemma foreach_ZS_down_cong rv e Vars from to step vars body body' H :
  (forall a pf vars, body a pf vars === body' a pf vars) ->
  @foreach_ZS_down rv e Vars from to step vars body H === foreach_ZS_down from to step vars body'.
intro EQ.
unfold foreach_ZS_down.
match goal with
| |- @foreach_ZS_down' _ _ _ _ _ _ _ _ _ ?pf _ _ === _ => generalize pf
end.
generalize 0 at 1 3 4 as off.
revert vars.
induction (S (Z.abs_nat (from - to))); intros; simpl.
* reflexivity.
* destruct (sumbool_of_bool (to <=? from + off)); auto.
  rewrite EQ.
  setoid_rewrite IHn.
  reflexivity.
Qed.

Local Opaque _limit_reduces.
Ltac gen_reduces :=
  match goal with |- context[@_limit_reduces ?a ?b ?c] => generalize (@_limit_reduces a b c) end.

Lemma whileST_cong {RV Vars E} vars measure cond cond' body body' :
  (forall vars, cond vars === cond' vars) ->
  (forall vars, body vars === body' vars) ->
  @whileST RV Vars E vars measure cond body === whileST vars measure cond' body'.
intros Econd Ebody.
unfold whileST.
generalize (measure vars) as limit. intro.
revert vars.
destruct (Z.le_decidable 0 limit).
* generalize (Zwf_guarded limit) as acc.
  apply Wf_Z.natlike_ind with (x := limit).
  + intros [acc] *; simpl.
    apply bindS_cong; auto.
    intros [|]; auto.
    apply bindS_cong; auto.
    intros. destruct (_limit_reduces _). simpl.
    reflexivity.
  + clear limit H.
    intros limit H IH [acc] vars s. simpl.
    destruct (Z_ge_dec _ _). 2: lia.
    apply bindS_cong; auto.
    intros [|]; auto.
    apply bindS_cong; auto.
    intros.
    gen_reduces.
    replace (Z.succ limit - 1) with limit. 2: lia. intro acc'.
    apply IH.
  + assumption.
* intros. simpl.
  destruct (Z_ge_dec _ _).
  + lia.
  + reflexivity.
Qed.

Lemma untilST_cong RV Vars E measure vars cond cond' (body body' : Vars -> monadS RV Vars E) :
  (forall vars, cond vars === cond' vars) ->
  (forall vars, body vars === body' vars) ->
  untilST vars measure cond body === untilST vars measure cond' body'.
intros Econd Ebody.
unfold untilST.
generalize (measure vars) as limit. intro.
revert vars.
destruct (Z.le_decidable 0 limit).
* generalize (Zwf_guarded limit) as acc.
  apply Wf_Z.natlike_ind with (x := limit).
  + intros [acc] * s; simpl.
    apply bindS_cong; auto.
    intros. apply bindS_cong; auto.
    intros [|]; auto.
    destruct (_limit_reduces _). simpl.
    reflexivity.
  + clear limit H.
    intros limit H IH [acc] vars s. simpl.
    destruct (Z_ge_dec _ _). 2: lia.
    apply bindS_cong; auto.
    intros. apply bindS_cong; auto.
    intros [|]; auto.
    gen_reduces.
    replace (Z.succ limit - 1) with limit. 2: lia. intro acc'.
    apply IH.
  + assumption.
* intros. simpl.
  destruct (Z_ge_dec _ _).
  + lia.
  + reflexivity.
Qed.

Lemma genlistS_cong {A RV E} f f' n :
  (forall i, f i === f' i) ->
  @genlistS A RV E f n === genlistS f' n.
intro H.
apply foreachS_cong.
intros. rewrite H.
reflexivity.
Qed.

Add Parametric Morphism {A RV E : Type} : (@genlistS A RV E)
  with signature equiv ==> eq ==> equiv as genlistS_morphism.
intros f g EQ n.
apply genlistS_cong.
auto.
Qed.

Lemma and_boolS_cong {RV E} x x' y y' :
  x === x' ->
  y === y' ->
  @and_boolS RV E x y === and_boolS x' y'.
intros E1 E2.
unfold and_boolS.
apply bindS_cong; auto.
intros [|]; auto.
Qed.

Lemma and_boolSP_cong {RV E P Q R} H x x' y y' :
  x === x' ->
  y === y' ->
  @and_boolSP RV E P Q R x y H === and_boolSP x' y'.
intros E1 E2.
unfold and_boolSP.
apply bindS_cong; auto.
intros [[|] [pf]]; auto.
apply bindS_cong; auto.
Qed.

Lemma or_boolS_cong {RV E} x x' y y' :
  x === x' ->
  y === y' ->
  @or_boolS RV E x y === or_boolS x' y'.
intros E1 E2.
unfold or_boolS.
apply bindS_cong; auto.
intros [|]; auto.
Qed.

Lemma or_boolSP_cong {RV E P Q R} H x x' y y' :
  x === x' ->
  y === y' ->
  @or_boolSP RV E P Q R x y H === or_boolSP x' y'.
intros E1 E2.
unfold or_boolSP.
apply bindS_cong; auto.
intros [[|] [pf]]; auto.
apply bindS_cong; auto.
Qed.

Lemma build_trivial_exS_cong {RV T E} x x' :
  x === x' ->
  @build_trivial_exS RV T E x === build_trivial_exS x'.
intros E1.
unfold build_trivial_exS.
apply bindS_cong; auto.
Qed.

Lemma liftRS_cong {A R Regs E} m m' :
  m === m' ->
  @liftRS A R Regs E m === liftRS m'.
intros E1.
unfold liftRS.
apply try_catchS_cong; auto.
Qed.

(* Monad lifting *)

Lemma liftState_bind Regval Regs A B E {r : Sail.Values.register_accessors Regs Regval} {m : monad Regval A E} {f : A -> monad Regval B E} :
  liftState r (bind m f) === bindS (liftState r m) (fun x => liftState r (f x)).
induction m; simpl; autorewrite with state; auto using bindS_cong.
Qed.
Hint Rewrite liftState_bind : liftState.
Hint Resolve liftState_bind : liftState.

Lemma liftState_bind0 Regval Regs B E {r : Sail.Values.register_accessors Regs Regval} {m : monad Regval unit E} {m' : monad Regval B E} :
  liftState r (bind0 m m') === seqS (liftState r m) (liftState r m').
induction m; simpl; autorewrite with state; auto using bindS_cong.
Qed.
Hint Rewrite liftState_bind0 : liftState.
Hint Resolve liftState_bind0 : liftState.

(* TODO: I want a general tactic for this, but abstracting the hint db out
   appears to break.
   This does beta reduction when no rules apply to try and allow more rules to apply
   (e.g., the application of f to x in the above lemma may introduce a beta redex). *)
(*Ltac rewrite_liftState := rewrite_strat topdown (choice (progress try hints liftState) progress eval cbn beta).*)

(* Set up some rewriting under congruences.  We would use
   rewrite_strat for this, but there are some issues, such as #10661
   where rewriting under if fails.  This is also the reason the hints
   above use Resolve as well as Rewrite.  These are intended for a
   goal of the form `term === ?evar`, e.g., from applying
   PrePostE_code_rw in Hoare. *)

Lemma eq_equiv A R (x y : A) (H : Equivalence R) :
  x = y -> @equiv A R H x y.
intro EQ; subst.
auto.
Qed.

Local Ltac tryrw db :=
  try (etransitivity; [solve [clear; eauto using eq_equiv with nocore db ] | ]; tryrw db).

Lemma if_bool_cong A (R : relation A) `{H:Equivalence _ R} (x x' y y' : A) (c : bool) :
  x === x' ->
  y === y' ->
  (if c then x else y) === if c then x' else y'.
intros E1 E2.
destruct c; auto. 
Qed.

Lemma if_sumbool_cong A P Q (R : relation A) `{H:Equivalence _ R} (x x' y y' : A) (c : sumbool P Q) :
  x === x' ->
  y === y' ->
  (if c then x else y) === if c then x' else y'.
intros E1 E2.
destruct c; auto. 
Qed.

Ltac statecong db :=
  tryrw db;
  lazymatch goal with
  | |- (_ >>$= _) === _ => eapply bindS_cong; intros; statecong db
  | |- (_ >>$ _) === _ => eapply seqS_cong; intros; statecong db
  | |- (if ?x then _ else _) === _ =>
       let ty := type of x in
       match ty with
       | bool => eapply if_bool_cong; statecong db
       | sumbool _ _ => eapply if_sumbool_cong; statecong db (* There's also a dependent case below *)
       | _ => apply equiv_reflexive
       end
  | |- (foreachS _ _ _) === _ =>
       solve [ eapply foreachS_cong; intros; statecong db ]
  | |- (foreach_ZS_up _ _ _ _ _) === _ =>
       solve [ eapply foreach_ZS_up_cong; intros; statecong db ]
  | |- (foreach_ZS_down _ _ _ _ _) === _ =>
       solve [ eapply foreach_ZS_down_cong; intros; statecong db ]
  | |- (genlistS _ _) === _ =>
       solve [ eapply genlistS_cong; intros; statecong db ]
  | |- (whileST _ _ _ _) === _ =>
       solve [ eapply whileST_cong; intros; statecong db ]
  | |- (untilST _ _ _ _) === _ =>
       solve [ eapply untilST_cong; intros; statecong db ]
  | |- (and_boolS _ _) === _ =>
       solve [ eapply and_boolS_cong; intros; statecong db ]
  | |- (or_boolS _ _) === _ =>
       solve [ eapply or_boolS_cong; intros; statecong db ]
  | |- (and_boolSP _ _) === _ =>
       solve [ eapply and_boolSP_cong; intros; statecong db ]
  | |- (or_boolSP _ _) === _ =>
       solve [ eapply or_boolSP_cong; intros; statecong db ]
  | |- (build_trivial_exS _) === _ =>
       solve [ eapply build_trivial_exS_cong; intros; statecong db ]
  | |- (liftRS _) === _ =>
       solve [ eapply liftRS_cong; intros; statecong db ]
  | |- (let '(matchvar1, matchvar2) := ?e1 in _) === _ =>
       eapply (@equiv_transitive _ _ _ _ (let '(matchvar1,matchvar2) := e1 in _) _);
       [ destruct e1; etransitivity; [ statecong db | apply equiv_reflexive ]
       | apply equiv_reflexive ]
  | |- (let '(existT _ matchvar1 matchvar2) := ?e1 in _) === _ =>
       eapply (@equiv_transitive _ _ _ _ (let '(existT _ matchvar1 matchvar2) := e1 in _) _);
       [ destruct e1; etransitivity; [ statecong db | apply equiv_reflexive ]
       | apply equiv_reflexive ]
  | |- (match ?e1 with None => _ | Some _ => _ end) === _ =>
       eapply (@equiv_transitive _ _ _ _ (match e1 with None => _ | Some _ => _ end) _);
       [ destruct e1; [> etransitivity; [> statecong db | apply equiv_reflexive ] ..]
       | apply equiv_reflexive ]
  | |- (match ?e1 with left _ => _ | right _ => _ end) === _ =>
       eapply (@equiv_transitive _ _ _ _ (match e1 with left _ => _ | right _ => _ end) _);
       [ destruct e1; [> etransitivity; [> statecong db | apply equiv_reflexive ] ..]
       | apply equiv_reflexive ]
  | |- ?X =>
       solve
       [ apply equiv_reflexive
       | apply eq_equiv; apply equiv_reflexive
       ]
  end.
Tactic Notation "statecong" ident(dbs) := statecong dbs.

Ltac rewrite_liftState :=
  match goal with
  | |- context [liftState ?r ?tm] =>
    try let H := fresh "H" in (eassert (H:liftState r tm === _); [ statecong liftState | rewrite H; clear H])
  end.

Lemma liftState_return Regval Regs A E {r : Sail.Values.register_accessors Regs Regval} {a :A} :
  liftState (E:=E) r (returnm a) = returnS a.
reflexivity.
Qed.
Hint Rewrite liftState_return : liftState.
Hint Resolve liftState_return : liftState.

(*
Lemma Value_liftState_Run:
  List.In (Value a, s') (liftState r m s)
  exists t, Run m t a.
  by (use assms in \<open>induction r m arbitrary: s s' rule: liftState.induct\<close>;
      simp add: failS_def throwS_def returnS_def del: read_regvalS.simps;
      blast elim: Value_bindS_elim)

lemmas liftState_if_distrib[liftState_simp] = if_distrib[where f = "liftState ra" for ra]
*)
Lemma liftState_if_distrib Regs Regval A E {r x y} {c : bool} :
  @liftState Regs Regval A E r (if c then x else y) = if c then liftState r x else liftState r y.
destruct c; reflexivity.
Qed.
Hint Resolve liftState_if_distrib : liftState.
(* TODO: try to find a way to make the above hint work when an alias is used for the
   monad type.  For some reason attempting to give a Resolve hint with a pattern doesn't
   work, but an Extern one works: *)
Hint Extern 0 (liftState _ _ = _) => simple apply liftState_if_distrib : liftState.
Lemma liftState_if_distrib_sumbool {Regs Regval A E P Q r x y} {c : sumbool P Q} :
  @liftState Regs Regval A E r (if c then x else y) = if c then liftState r x else liftState r y.
destruct c; reflexivity.
Qed.
Hint Resolve liftState_if_distrib_sumbool : liftState.
(* As above, but simple apply doesn't seem to work (again, due to unification problems
   with the M alias for monad).  Be careful about only applying to a suitable goal to
   avoid slowing down proofs. *)
Hint Extern 0 (liftState _ ?t = _) =>
  match t with
  | match ?x with _ => _ end =>
    match type of x with
    | sumbool _ _ => apply liftState_if_distrib_sumbool
    end
  end : liftState.

Lemma liftState_match_distrib_sumbool {Regs Regval A E P Q r x y} {c : sumbool P Q} :
  @liftState Regs Regval A E r (match c with left H => x H | right H => y H end) = match c with left H => liftState r (x H) | right H => liftState r (y H) end.
destruct c; reflexivity.
Qed.
(* As above, but also need to beta reduce H into x and y. *)
Hint Extern 0 (liftState _ ?t = _) =>
  match t with
  | match ?x with _ => _ end =>
    match type of x with
    | sumbool _ _ => etransitivity; [apply liftState_match_distrib_sumbool | cbv beta; reflexivity ]
    end
  end : liftState.

Lemma liftState_let_pair Regs RegVal A B C E r (x : B * C) M :
  @liftState Regs RegVal A E r (let '(y, z) := x in M y z) =
  let '(y, z) := x in liftState r (M y z).
destruct x.
reflexivity.
Qed.
Hint Extern 0 (liftState _ (let '(x,y) := _ in _) = _) =>
  (rewrite liftState_let_pair; reflexivity) : liftState.

Lemma liftState_let_Tpair Regs RegVal A B (P : B -> Prop) E r (x : sigT P) M :
  @liftState Regs RegVal A E r (let '(existT _ y z) := x in M y z) =
  let '(existT _ y z) := x in liftState r (M y z).
destruct x.
reflexivity.
Qed.
Hint Extern 0 (liftState _ (let '(existT _ x y) := _ in _) = _) =>
  (rewrite liftState_let_Tpair; reflexivity) : liftState.

Lemma liftState_opt_match Regs RegVal A B E (x : option A) m f r :
  @liftState Regs RegVal B E r (match x with None => m | Some v => f v end) =
  match x with None => liftState r m | Some v => liftState r (f v) end.
destruct x; reflexivity.
Qed.
Hint Extern 0 (liftState _ (match _ with None => _ | Some _ => _ end) = _) =>
  (rewrite liftState_opt_match; reflexivity) : liftState.

Lemma Value_bindS_iff {Regs A B E} {f : A -> monadS Regs B E} {b m s s''} :
  List.In (Value b, s'') (bindS m f s) <-> (exists a s', List.In (Value a, s') (m s) /\ List.In (Value b, s'') (f a s')).
split.
* intro H.
  apply bindS_cases in H.
  destruct H as [(? & ? & ? & [= <-] & ? & ?) | [(? & [= <-] & ?) | (? & ? & ? & [= <-] & ? & ?)]];
  eauto.
* intros (? & ? & ? & ?).
  eauto with bindS_intros.
Qed.

Lemma Ex_bindS_iff {Regs A B E} {f : A -> monadS Regs B E} {m e s s''} :
  List.In (Ex e, s'') (bindS m f s) <-> List.In (Ex e, s'') (m s) \/ (exists a s', List.In (Value a, s') (m s) /\ List.In (Ex e, s'') (f a s')).
split.
* intro H.
  apply bindS_cases in H.
  destruct H as [(? & ? & ? & [= <-] & ? & ?) | [(? & [= <-] & ?) | (? & ? & ? & [= <-] & ? & ?)]];
  eauto.
* intros [H | (? & ? & H1 & H2)];
  eauto with bindS_intros.
Qed.

Lemma liftState_throw Regs Regval A E {r} {e : E} :
  @liftState Regval Regs A E r (throw e) = throwS e.
reflexivity.
Qed.
Lemma liftState_assert Regs Regval E {r c msg} :
  @liftState Regval Regs _ E r (assert_exp c msg) = assert_expS c msg.
destruct c; reflexivity.
Qed.
Lemma liftState_assert' Regs Regval E {r c msg} :
  @liftState Regval Regs _ E r (assert_exp' c msg) = assert_expS' c msg.
destruct c; reflexivity.
Qed.
Lemma liftState_exit Regs Regval A E r :
  @liftState Regval Regs A E r (exit tt) = exitS tt.
reflexivity.
Qed.
Lemma liftState_exclResult Regs Regval E r :
  @liftState Regs Regval _ E r (excl_result tt) = excl_resultS tt.
reflexivity.
Qed.
Lemma liftState_barrier Regs Regval E r bk :
  @liftState Regs Regval _ E r (barrier bk) = returnS tt.
reflexivity.
Qed.
Lemma liftState_footprint Regs Regval E r :
  @liftState Regs Regval _ E r (footprint tt) = returnS tt.
reflexivity.
Qed.
Lemma liftState_choose_bool Regs Regval E r descr :
  @liftState Regs Regval _ E r (choose_bool descr) = choose_boolS tt.
reflexivity.
Qed.
(*declare undefined_boolS_def[simp]*)
Lemma liftState_undefined Regs Regval E r :
  @liftState Regs Regval _ E r (undefined_bool tt) = undefined_boolS tt.
reflexivity.
Qed.
Lemma liftState_maybe_fail Regs Regval A E r msg x :
  @liftState Regs Regval A E r (maybe_fail msg x) = maybe_failS msg x.
destruct x; reflexivity.
Qed.
Lemma liftState_and_boolM Regs Regval E r x y :
  @liftState Regs Regval _ E r (and_boolM x y) === and_boolS (liftState r x) (liftState r y).
unfold and_boolM, and_boolS.
rewrite_liftState.
reflexivity.
Qed.
Lemma liftState_and_boolMP Regs Regval E P Q R r x y H :
  @liftState Regs Regval _ E r (@and_boolMP _ _ P Q R x y H) === and_boolSP (liftState r x) (liftState r y).
unfold and_boolMP, and_boolSP.
rewrite liftState_bind.
apply bindS_cong; auto.
intros [[|] [A]].
* rewrite liftState_bind.
  simpl;
  apply bindS_cong; auto.
  intros [a' A'].
  rewrite liftState_return.
  reflexivity.
* rewrite liftState_return.
  reflexivity.
Qed.

Lemma liftState_or_boolM Regs Regval E r x y :
  @liftState Regs Regval _ E r (or_boolM x y) === or_boolS (liftState r x) (liftState r y).
unfold or_boolM, or_boolS.
rewrite liftState_bind.
apply bindS_cong; auto.
intros. rewrite liftState_if_distrib.
reflexivity.
Qed.
Lemma liftState_or_boolMP Regs Regval E P Q R r x y H :
  @liftState Regs Regval _ E r (@or_boolMP _ _ P Q R x y H) === or_boolSP (liftState r x) (liftState r y).
unfold or_boolMP, or_boolSP.
rewrite liftState_bind.
simpl.
apply bindS_cong; auto.
intros [[|] [A]].
* rewrite liftState_return.
  reflexivity.
* rewrite liftState_bind;
  simpl;
  apply bindS_cong; auto;
  intros [a' A'];
  rewrite liftState_return;
  reflexivity.
Qed.

Lemma liftState_build_trivial_ex Regs Regval E T r m :
  @liftState Regs Regval _ E r (@build_trivial_ex _ _ T m) ===
    build_trivial_exS (liftState r m).
unfold build_trivial_ex, build_trivial_exS.
unfold ArithFact.
intro.
rewrite liftState_bind.
reflexivity.
Qed.

Hint Rewrite liftState_throw liftState_assert liftState_assert' liftState_exit
             liftState_exclResult liftState_barrier liftState_footprint
             liftState_choose_bool liftState_undefined liftState_maybe_fail
             liftState_and_boolM liftState_and_boolMP
             liftState_or_boolM liftState_or_boolMP
             liftState_build_trivial_ex
           : liftState.
Hint Resolve liftState_throw liftState_assert liftState_assert' liftState_exit
             liftState_exclResult liftState_barrier liftState_footprint
             liftState_choose_bool liftState_undefined liftState_maybe_fail
             liftState_and_boolM liftState_and_boolMP
             liftState_or_boolM liftState_or_boolMP
             liftState_build_trivial_ex
           : liftState.

Lemma liftState_try_catch Regs Regval A E1 E2 r m h :
  @liftState Regs Regval A E2 r (try_catch (E1 := E1) m h) === try_catchS (liftState r m) (fun e => liftState r (h e)).
induction m; intros; simpl; autorewrite with state;
solve
[ auto
| erewrite try_catchS_bindS_no_throw; intros;
  only 2,3: (autorewrite with ignore_throw; reflexivity);
  apply bindS_cong; auto
].
Qed.
Hint Rewrite liftState_try_catch : liftState.
Hint Resolve liftState_try_catch : liftState.

Lemma liftState_early_return Regs Regval A R E r x :
  liftState (Regs := Regs) r (@early_return Regval A R E x) = early_returnS x.
reflexivity.
Qed.
Hint Rewrite liftState_early_return : liftState.
Hint Resolve liftState_early_return : liftState.

Lemma liftState_catch_early_return (*[liftState_simp]:*) Regs Regval A E r m :
  liftState (Regs := Regs) r (@catch_early_return Regval A E m) === catch_early_returnS (liftState r m).
unfold catch_early_return, catch_early_returnS.
rewrite_liftState.
apply try_catchS_cong; auto.
intros [a | e] s'; auto.
Qed.
Hint Rewrite liftState_catch_early_return : liftState.
Hint Resolve liftState_catch_early_return : liftState.

Lemma liftState_liftR Regs Regval A R E r m :
  liftState (Regs := Regs) r (@liftR Regval A R E m) === liftRS (liftState r m).
unfold liftR, liftRS.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_liftR : liftState.
Hint Resolve liftState_liftR : liftState.

Lemma liftState_try_catchR Regs Regval A R E1 E2 r m h :
  liftState (Regs := Regs) r (@try_catchR Regval A R E1 E2 m h) === try_catchRS (liftState r m) (fun x => liftState r (h x)).
unfold try_catchR, try_catchRS. rewrite_liftState.
apply try_catchS_cong; auto.
intros [r' | e] s'; auto.
Qed.
Hint Rewrite liftState_try_catchR : liftState.
Hint Resolve liftState_try_catchR : liftState.

Lemma liftState_bool_of_bitU_nondet Regs Regval E r b :
  liftState (Regs := Regs) r (@bool_of_bitU_nondet Regval E b) = bool_of_bitU_nondetS b.
destruct b; simpl; try reflexivity.
Qed.
Hint Rewrite liftState_bool_of_bitU_nondet : liftState.
Hint Resolve liftState_bool_of_bitU_nondet : liftState.

Lemma liftState_read_memt Regs Regval A B E H rk a sz r :
  liftState (Regs := Regs) r (@read_memt Regval A B E H rk a sz) === read_memtS rk a sz.
unfold read_memt, read_memt_bytes, read_memtS, maybe_failS. simpl.
apply bindS_cong; auto.
intros [byte bit].
destruct (option_map _); auto.
Qed.
Hint Rewrite liftState_read_memt : liftState.
Hint Resolve liftState_read_memt : liftState.

Lemma liftState_read_mem Regs Regval A B E H rk asz a sz r :
  liftState (Regs := Regs) r (@read_mem Regval A B E H rk asz a sz) === read_memS rk a sz.
unfold read_mem, read_memS, read_memtS. simpl.
unfold read_mem_bytesS, read_memt_bytesS.
repeat rewrite bindS_assoc.
apply bindS_cong; auto.
intros [ bytes | ]; auto. simpl.
apply bindS_cong; auto.
intros [byte bit].
rewrite bindS_returnS_left. rewrite_liftState.
destruct (option_map _); auto.
Qed.
Hint Rewrite liftState_read_mem : liftState.
Hint Resolve liftState_read_mem : liftState.

Lemma liftState_write_mem_ea Regs Regval A E rk asz a sz r :
  liftState (Regs := Regs) r (@write_mem_ea Regval A E rk asz a sz) = returnS tt.
reflexivity.
Qed.
Hint Rewrite liftState_write_mem_ea : liftState.
Hint Resolve liftState_write_mem_ea : liftState.

Lemma liftState_write_memt Regs Regval A B E wk addr sz v t r :
  liftState (Regs := Regs) r (@write_memt Regval A B E wk addr sz v t) = write_memtS wk addr sz v t.
unfold write_memt, write_memtS.
destruct (Sail.Values.mem_bytes_of_bits v); auto.
Qed.
Hint Rewrite liftState_write_memt : liftState.
Hint Resolve liftState_write_memt : liftState.

Lemma liftState_write_mem Regs Regval A B E wk addrsize addr sz v r :
  liftState (Regs := Regs) r (@write_mem Regval A B E wk addrsize addr sz v) = write_memS wk addr sz v.
unfold write_mem, write_memS, write_memtS.
destruct (Sail.Values.mem_bytes_of_bits v); simpl; auto.
Qed.
Hint Rewrite liftState_write_mem : liftState.
Hint Resolve liftState_write_mem : liftState.

Lemma bindS_rw_left Regs A B E m1 m2 (f : A -> monadS Regs B E) s :
  m1 s = m2 s ->
  bindS m1 f s = bindS m2 f s.
intro H. unfold bindS. rewrite H. reflexivity.
Qed. 

Lemma liftState_read_reg_readS Regs Regval A E reg get_regval' set_regval' :
  (forall s, map_bind reg.(of_regval) (get_regval' reg.(name) s) = Some (reg.(read_from) s)) ->
  liftState (Regs := Regs) (get_regval', set_regval') (@read_reg _ Regval A E reg) === readS (fun x => reg.(read_from) (ss_regstate x)).
intros.
unfold read_reg. simpl. unfold readS. intro s.
erewrite bindS_rw_left. 2: {
  apply bindS_returnS_left.
}
specialize (H (ss_regstate s)).
destruct (get_regval' _ _) as [v | ]; only 2: discriminate H.
rewrite bindS_returnS_left.
simpl in *.
rewrite H.
reflexivity.
Qed.

(* Generic tactic to apply liftState to register reads, so that we don't have to
   generate lots of model-specific lemmas.  This takes advantage of the fact that
   if you fix the register then the lemma above is trivial by convertability. *)

Ltac lift_read_reg :=
  match goal with
  | |- context [liftState ?r (@read_reg ?s ?rv ?a ?e ?ref)] =>
         let f := eval simpl in (fun x => (read_from ref) (ss_regstate x)) in
         change (liftState r (@read_reg s rv a e ref)) with (@readS s a e f)
  end.

Hint Extern 1 (liftState _ (read_reg _) === _) => lift_read_reg; reflexivity : liftState.

Lemma liftState_write_reg_updateS Regs Regval A E get_regval' set_regval' reg (v : A) :
  (forall s, set_regval' (name reg) (regval_of reg v) s = Some (write_to reg v s)) ->
  liftState (Regs := Regs) (Regval := Regval) (E := E) (get_regval', set_regval') (write_reg reg v) === updateS (fun s => {| ss_regstate := (write_to reg v s.(ss_regstate)); ss_memstate := s.(ss_memstate); ss_tagstate := s.(ss_tagstate) |}).
intros. intro s.
unfold write_reg. simpl. unfold readS, seqS.
erewrite bindS_rw_left. 2: {
  apply bindS_returnS_left.
}
specialize (H (ss_regstate s)).
destruct (set_regval' _ _) as [v' | ]; only 2: discriminate H.
injection H as H1.
unfold updateS.
rewrite <- H1.
reflexivity.
Qed.
(*
Lemma liftState_iter_aux Regs Regval A E :
  liftState r (iter_aux i f xs) = iterS_aux i (fun i x => liftState r (f i x)) xs.
  by (induction i "\<lambda>i x. liftState r (f i x)" xs rule: iterS_aux.induct)
     (auto simp: liftState_simp cong: bindS_cong)
Hint Rewrite liftState_iter_aux : liftState.
Hint Resolve liftState_iter_aux : liftState.

lemma liftState_iteri[liftState_simp]:
  "liftState r (iteri f xs) = iteriS (\<lambda>i x. liftState r (f i x)) xs"
  by (auto simp: iteri_def iteriS_def liftState_simp)

lemma liftState_iter[liftState_simp]:
  "liftState r (iter f xs) = iterS (liftState r \<circ> f) xs"
  by (auto simp: iter_def iterS_def liftState_simp)
*)
Lemma liftState_foreachM Regs Regval A Vars E (xs : list A) (vars : Vars) (body : A -> Vars -> monad Regval Vars E) r :
  liftState (Regs := Regs) r (foreachM xs vars body) === foreachS xs vars (fun x vars => liftState r (body x vars)).
revert vars.
induction xs as [ | h t].
* reflexivity.
* intros vars. simpl.
  rewrite_liftState.
  apply bindS_cong; auto.
Qed.
Hint Rewrite liftState_foreachM : liftState.
Hint Resolve liftState_foreachM : liftState.

Lemma liftState_foreach_ZM_up Regs Regval Vars E from to step vars body H r :
  liftState (Regs := Regs) r
    (@foreach_ZM_up Regval E Vars from to step vars body H) ===
     foreach_ZS_up from to step vars (fun z H' a => liftState r (body z H' a)).
unfold foreach_ZM_up, foreach_ZS_up.
match goal with
| |- liftState _ (@foreach_ZM_up' _ _ _ _ _ _ _ _ _ ?pf _ _) === _ => generalize pf
end.
generalize 0 at 2 3 4 as off.
revert vars.
induction (S (Z.abs_nat (from - to))); intros.
* simpl.
  rewrite_liftState.
  reflexivity.
* simpl.
  rewrite_liftState.
  destruct (sumbool_of_bool (from + off <=? to)); auto.
  repeat replace_ArithFact_proof.
  reflexivity.
Qed.
Hint Rewrite liftState_foreach_ZM_up : liftState.
Hint Resolve liftState_foreach_ZM_up : liftState.

Lemma liftState_foreach_ZM_down Regs Regval Vars E from to step vars body H r :
  liftState (Regs := Regs) r
    (@foreach_ZM_down Regval E Vars from to step vars body H) ===
     foreach_ZS_down from to step vars (fun z H' a => liftState r (body z H' a)).
unfold foreach_ZM_down, foreach_ZS_down.
match goal with
| |- liftState _ (@foreach_ZM_down' _ _ _ _ _ _ _ _ _ ?pf _ _) === _ => generalize pf
end.
generalize 0 at 1 3 4 as off.
revert vars.
induction (S (Z.abs_nat (from - to))); intros.
* simpl.
  rewrite_liftState.
  reflexivity.
* simpl.
  rewrite_liftState.
  destruct (sumbool_of_bool (to <=? from + off)); auto.
  repeat replace_ArithFact_proof.
  reflexivity.
Qed.
Hint Rewrite liftState_foreach_ZM_down : liftState.
Hint Resolve liftState_foreach_ZM_down : liftState.

Lemma liftState_genlistM Regs Regval A E r f n :
  liftState (Regs := Regs) r (@genlistM A Regval E f n) === genlistS (fun x => liftState r (f x)) n.
unfold genlistM, genlistS.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_genlistM : liftState.
Hint Resolve liftState_genlistM : liftState.

Lemma liftState_choose_bools Regs Regval E descr n r :
  liftState (Regs := Regs) r (@choose_bools Regval E descr n) === choose_boolsS n.
unfold choose_bools, choose_boolsS.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_choose_bools : liftState.
Hint Resolve liftState_choose_bools : liftState.

Lemma liftState_bools_of_bits_nondet Regs Regval E r bs :
  liftState (Regs := Regs) r (@bools_of_bits_nondet Regval E bs) === bools_of_bits_nondetS bs.
unfold bools_of_bits_nondet, bools_of_bits_nondetS.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_bools_of_bits_nondet : liftState.
Hint Resolve liftState_bools_of_bits_nondet : liftState.

Lemma liftState_internal_pick Regs Regval A E r (xs : list A) :
  liftState (Regs := Regs) (Regval := Regval) (E := E) r (internal_pick xs) === internal_pickS xs.
unfold internal_pick, internal_pickS.
unfold choose.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_internal_pick : liftState.
Hint Resolve liftState_internal_pick : liftState.

Lemma liftState_undefined_word_nat Regs Regval E r n :
  liftState (Regs := Regs) (Regval := Regval) (E := E) r (undefined_word_nat n) === undefined_word_natS n.
induction n.
* reflexivity.
* simpl.
  apply bindS_cong; auto.
  intro. 
  rewrite_liftState.
  apply bindS_cong; auto.
Qed.
Hint Rewrite liftState_undefined_word_nat : liftState.
Hint Resolve liftState_undefined_word_nat : liftState.

Lemma liftState_undefined_bitvector Regs Regval E r n `{ArithFact (n >=? 0)} :
  liftState (Regs := Regs) (Regval := Regval) (E := E) r (undefined_bitvector n) === undefined_bitvectorS n.
unfold undefined_bitvector, undefined_bitvectorS.
rewrite_liftState.
reflexivity.
Qed.
Hint Rewrite liftState_undefined_bitvector : liftState.
Hint Resolve liftState_undefined_bitvector : liftState.

Lemma liftRS_returnS (*[simp]:*) A R Regs E x :
  @liftRS A R Regs E (returnS x) = returnS x.
reflexivity.
Qed.

Lemma concat_singleton A (xs : list A) :
  concat (xs::nil) = xs.
simpl.
rewrite app_nil_r.
reflexivity.
Qed.

Lemma liftRS_bindS Regs A B R E (m : monadS Regs A E) (f : A -> monadS Regs B E) :
  @liftRS B R Regs E (bindS m f) === bindS (liftRS m) (fun x => liftRS (f x)).
intro s.
unfold liftRS, try_catchS, bindS, throwS, returnS.
induction (m s) as [ | [[a | [msg | e]] t]].
* reflexivity.
* simpl. rewrite flat_map_app. rewrite IHl. reflexivity.
* simpl. rewrite IHl. reflexivity.
* simpl. rewrite IHl. reflexivity.
Qed.

Lemma liftRS_assert_expS_True (*[simp]:*) Regs R E msg :
  @liftRS _ R Regs E (assert_expS true msg) = returnS tt.
reflexivity.
Qed.

(*
lemma untilM_domI:
  fixes V :: "'vars \<Rightarrow> nat"
  assumes "Inv vars"
    and "\<And>vars t vars' t'. \<lbrakk>Inv vars; Run (body vars) t vars'; Run (cond vars') t' False\<rbrakk> \<Longrightarrow> V vars' < V vars \<and> Inv vars'"
  shows "untilM_dom (vars, cond, body)"
  using assms
  by (induction vars rule: measure_induct_rule[where f = V])
     (auto intro: untilM.domintros)

lemma untilM_dom_untilS_dom:
  assumes "untilM_dom (vars, cond, body)"
  shows "untilS_dom (vars, liftState r \<circ> cond, liftState r \<circ> body, s)"
  using assms
  by (induction vars cond body arbitrary: s rule: untilM.pinduct)
     (rule untilS.domintros, auto elim!: Value_liftState_Run)

lemma measure2_induct:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> nat"
  assumes "\<And>x1 y1. (\<And>x2 y2. f x2 y2 < f x1 y1 \<Longrightarrow> P x2 y2) \<Longrightarrow> P x1 y1"
  shows "P x y"
proof -
  have "P (fst x) (snd x)" for x
    by (induction x rule: measure_induct_rule[where f = "\<lambda>x. f (fst x) (snd x)"]) (auto intro: assms)
  then show ?thesis by auto
qed

lemma untilS_domI:
  fixes V :: "'vars \<Rightarrow> 'regs sequential_state \<Rightarrow> nat"
  assumes "Inv vars s"
    and "\<And>vars s vars' s' s''.
           \<lbrakk>Inv vars s; (Value vars', s') \<in> body vars s; (Value False, s'') \<in> cond vars' s'\<rbrakk>
            \<Longrightarrow> V vars' s'' < V vars s \<and> Inv vars' s''"
  shows "untilS_dom (vars, cond, body, s)"
  using assms
  by (induction vars s rule: measure2_induct[where f = V])
     (auto intro: untilS.domintros)

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
*)


Lemma liftState_whileM RV Vars E r measure vars cond (body : Vars -> monad RV Vars E) :
  liftState (Regs := RV) r (whileMT vars measure cond body) === whileST vars measure (fun vars => liftState r (cond vars)) (fun vars => liftState r (body vars)).
unfold whileMT, whileST.
generalize (measure vars) as limit. intro.
revert vars.
destruct (Z.le_decidable 0 limit).
* generalize (Zwf_guarded limit) at 1 as acc1.
  generalize (Zwf_guarded limit) at 1 as acc2.
  apply Wf_Z.natlike_ind with (x := limit).
  + intros [acc1] [acc2] *; simpl.
    rewrite_liftState.
    apply bindS_cong; auto.
    intros [|]; auto.
    apply bindS_cong; auto.
    intros. repeat destruct (_limit_reduces _). simpl.
    reflexivity.
  + clear limit H.
    intros limit H IH [acc1] [acc2] vars s. simpl.
    destruct (Z_ge_dec _ _). 2: lia.
    rewrite_liftState.
    apply bindS_cong; auto.
    intros [|]; auto.
    apply bindS_cong; auto.
    intros.
    repeat gen_reduces.
    replace (Z.succ limit - 1) with limit. 2: lia. intros acc1' acc2'.
    apply IH.
  + assumption.
* intros. simpl.
  destruct (Z_ge_dec _ _).
  + lia.
  + reflexivity.
Qed.
Hint Resolve liftState_whileM : liftState.

(*
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
qed*)

Lemma liftState_untilM RV Vars E r measure vars cond (body : Vars -> monad RV Vars E) :
  liftState (Regs := RV) r (untilMT vars measure cond body) === untilST vars measure (fun vars => liftState r (cond vars)) (fun vars => liftState r (body vars)).
unfold untilMT, untilST.
generalize (measure vars) as limit. intro.
revert vars.
destruct (Z.le_decidable 0 limit).
* generalize (Zwf_guarded limit) at 1 as acc1.
  generalize (Zwf_guarded limit) at 1 as acc2.
  apply Wf_Z.natlike_ind with (x := limit).
  + intros [acc1] [acc2] * s; simpl.
    rewrite_liftState.
    apply bindS_cong; auto.
    intros. apply bindS_cong; auto.
    intros [|]; auto.
    repeat destruct (_limit_reduces _). simpl.
    reflexivity.
  + clear limit H.
    intros limit H IH [acc1] [acc2] vars s. simpl.
    destruct (Z_ge_dec _ _). 2: lia.
    rewrite_liftState.
    apply bindS_cong; auto.
    intros. apply bindS_cong; auto.
    intros [|]; auto.
    repeat gen_reduces.
    replace (Z.succ limit - 1) with limit. 2: lia. intros acc1' acc2'.
    apply IH.
  + assumption.
* intros. simpl.
  destruct (Z_ge_dec _ _).
  + lia.
  + reflexivity.
Qed.
Hint Resolve liftState_untilM : liftState.

(*

text \<open>Simplification rules for monadic Boolean connectives\<close>

lemma if_return_return[simp]: "(if a then return True else return False) = return a" by auto

lemma and_boolM_simps[simp]:
  "and_boolM (return b) (return c) = return (b \<and> c)"
  "and_boolM x (return True) = x"
  "and_boolM x (return False) = x \<bind> (\<lambda>_. return False)"
  "\<And>x y z. and_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. and_boolM (y r) z))"
  by (auto simp: and_boolM_def)

lemma and_boolM_return_if:
  "and_boolM (return b) y = (if b then y else return False)"
  by (auto simp: and_boolM_def)

lemma and_boolM_return_return_and[simp]: "and_boolM (return l) (return r) = return (l \<and> r)"
  by (auto simp: and_boolM_def)

lemmas and_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolM x y" for y]

lemma or_boolM_simps[simp]:
  "or_boolM (return b) (return c) = return (b \<or> c)"
  "or_boolM x (return True) = x \<bind> (\<lambda>_. return True)"
  "or_boolM x (return False) = x"
  "\<And>x y z. or_boolM (x \<bind> y) z = (x \<bind> (\<lambda>r. or_boolM (y r) z))"
  by (auto simp: or_boolM_def)

lemma or_boolM_return_if:
  "or_boolM (return b) y = (if b then return True else y)"
  by (auto simp: or_boolM_def)

lemma or_boolM_return_return_or[simp]: "or_boolM (return l) (return r) = return (l \<or> r)"
  by (auto simp: or_boolM_def)

lemmas or_boolM_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolM x y" for y]

lemma if_returnS_returnS[simp]: "(if a then returnS True else returnS False) = returnS a" by auto

lemma and_boolS_simps[simp]:
  "and_boolS (returnS b) (returnS c) = returnS (b \<and> c)"
  "and_boolS x (returnS True) = x"
  "and_boolS x (returnS False) = bindS x (\<lambda>_. returnS False)"
  "\<And>x y z. and_boolS (bindS x y) z = (bindS x (\<lambda>r. and_boolS (y r) z))"
  by (auto simp: and_boolS_def)

lemma and_boolS_returnS_if:
  "and_boolS (returnS b) y = (if b then y else returnS False)"
  by (auto simp: and_boolS_def)

lemmas and_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. and_boolS x y" for y]

lemma and_boolS_returnS_True[simp]: "and_boolS (returnS True) c = c"
  by (auto simp: and_boolS_def)

lemma or_boolS_simps[simp]:
  "or_boolS (returnS b) (returnS c) = returnS (b \<or> c)"
  "or_boolS (returnS False) m = m"
  "or_boolS x (returnS True) = bindS x (\<lambda>_. returnS True)"
  "or_boolS x (returnS False) = x"
  "\<And>x y z. or_boolS (bindS x y) z = (bindS x (\<lambda>r. or_boolS (y r) z))"
  by (auto simp: or_boolS_def)

lemma or_boolS_returnS_if:
  "or_boolS (returnS b) y = (if b then returnS True else y)"
  by (auto simp: or_boolS_def)

lemmas or_boolS_if_distrib[simp] = if_distrib[where f = "\<lambda>x. or_boolS x y" for y]

lemma Run_or_boolM_E:
  assumes "Run (or_boolM l r) t a"
  obtains "Run l t True" and "a"
  | tl tr where "Run l tl False" and "Run r tr a" and "t = tl @ tr"
  using assms by (auto simp: or_boolM_def elim!: Run_bindE Run_ifE Run_returnE)

lemma Run_and_boolM_E:
  assumes "Run (and_boolM l r) t a"
  obtains "Run l t False" and "\<not>a"
  | tl tr where "Run l tl True" and "Run r tr a" and "t = tl @ tr"
  using assms by (auto simp: and_boolM_def elim!: Run_bindE Run_ifE Run_returnE)

lemma maybe_failS_Some[simp]: "maybe_failS msg (Some v) = returnS v"
  by (auto simp: maybe_failS_def)

text \<open>Event traces\<close>

lemma Some_eq_bind_conv: "Some x = Option.bind f g \<longleftrightarrow> (\<exists>y. f = Some y \<and> g y = Some x)"
  unfolding bind_eq_Some_conv[symmetric] by auto

lemma if_then_Some_eq_Some_iff: "((if b then Some x else None) = Some y) \<longleftrightarrow> (b \<and> y = x)"
  by auto

lemma Some_eq_if_then_Some_iff: "(Some y = (if b then Some x else None)) \<longleftrightarrow> (b \<and> y = x)"
  by auto

lemma emitEventS_update_cases:
  assumes "emitEventS ra e s = Some s'"
  obtains
    (Write_mem) wk addr sz v tag r
      where "e = E_write_memt wk addr sz v tag r \<or> (e = E_write_mem wk addr sz v r \<and> tag = B0)"
        and "s' = put_mem_bytes addr sz v tag s"
  | (Write_reg) r v rs'
      where "e = E_write_reg r v" and "(snd ra) r v (regstate s) = Some rs'"
        and "s' = s\<lparr>regstate := rs'\<rparr>"
  | (Read) "s' = s"
  using assms
  by (elim emitEventS.elims)
     (auto simp: Some_eq_bind_conv bind_eq_Some_conv if_then_Some_eq_Some_iff Some_eq_if_then_Some_iff)

lemma runTraceS_singleton[simp]: "runTraceS ra [e] s = emitEventS ra e s"
  by (cases "emitEventS ra e s"; auto)

lemma runTraceS_ConsE:
  assumes "runTraceS ra (e # t) s = Some s'"
  obtains s'' where "emitEventS ra e s = Some s''" and "runTraceS ra t s'' = Some s'"
  using assms by (auto simp: bind_eq_Some_conv)

lemma runTraceS_ConsI:
  assumes "emitEventS ra e s = Some s'" and "runTraceS ra t s' = Some s''"
  shows "runTraceS ra (e # t) s = Some s''"
  using assms by auto

lemma runTraceS_Cons_tl:
  assumes "emitEventS ra e s = Some s'"
  shows "runTraceS ra (e # t) s = runTraceS ra t s'"
  using assms by (elim emitEventS.elims) (auto simp: Some_eq_bind_conv bind_eq_Some_conv)

lemma runTraceS_appendE:
  assumes "runTraceS ra (t @ t') s = Some s'"
  obtains s'' where "runTraceS ra t s = Some s''" and "runTraceS ra t' s'' = Some s'"
proof -
  have "\<exists>s''. runTraceS ra t s = Some s'' \<and> runTraceS ra t' s'' = Some s'"
  proof (use assms in \<open>induction t arbitrary: s\<close>)
    case (Cons e t)
    from Cons.prems
    obtain s_e where "emitEventS ra e s = Some s_e" and "runTraceS ra (t @ t') s_e = Some s'"
      by (auto elim: runTraceS_ConsE simp: bind_eq_Some_conv)
    with Cons.IH[of s_e] show ?case by (auto intro: runTraceS_ConsI)
  qed auto
  then show ?thesis using that by blast
qed

lemma runTraceS_nth_split:
  assumes "runTraceS ra t s = Some s'" and n: "n < length t"
  obtains s1 s2 where "runTraceS ra (take n t) s = Some s1"
    and "emitEventS ra (t ! n) s1 = Some s2"
    and "runTraceS ra (drop (Suc n) t) s2 = Some s'"
proof -
  have "runTraceS ra (take n t @ t ! n # drop (Suc n) t) s = Some s'"
    using assms
    by (auto simp: id_take_nth_drop[OF n, symmetric])
  then show thesis by (blast elim: runTraceS_appendE runTraceS_ConsE intro: that)
qed

text \<open>Memory accesses\<close>

lemma get_mem_bytes_put_mem_bytes_same_addr:
  assumes "length v = sz"
  shows "get_mem_bytes addr sz (put_mem_bytes addr sz v tag s) = Some (v, if sz > 0 then tag else B1)"
proof (unfold assms[symmetric], induction v rule: rev_induct)
  case Nil
  then show ?case by (auto simp: get_mem_bytes_def)
next
  case (snoc x xs)
  then show ?case
    by (cases tag)
       (auto simp: get_mem_bytes_def put_mem_bytes_def Let_def and_bit_eq_iff foldl_and_bit_eq_iff
             cong: option.case_cong split: if_splits option.splits)
qed

lemma memstate_put_mem_bytes:
  assumes "length v = sz"
  shows "memstate (put_mem_bytes addr sz v tag s) addr' =
         (if addr' \<in> {addr..<addr+sz} then Some (v ! (addr' - addr)) else memstate s addr')"
  unfolding assms[symmetric]
  by (induction v rule: rev_induct) (auto simp: put_mem_bytes_def nth_Cons nth_append Let_def)

lemma tagstate_put_mem_bytes:
  assumes "length v = sz"
  shows "tagstate (put_mem_bytes addr sz v tag s) addr' =
         (if addr' \<in> {addr..<addr+sz} then Some tag else tagstate s addr')"
  unfolding assms[symmetric]
  by (induction v rule: rev_induct) (auto simp: put_mem_bytes_def nth_Cons nth_append Let_def)

lemma get_mem_bytes_cong:
  assumes "\<forall>addr'. addr \<le> addr' \<and> addr' < addr + sz \<longrightarrow>
                   (memstate s' addr' = memstate s addr' \<and> tagstate s' addr' = tagstate s addr')"
  shows "get_mem_bytes addr sz s' = get_mem_bytes addr sz s"
proof (use assms in \<open>induction sz\<close>)
  case 0
  then show ?case by (auto simp: get_mem_bytes_def)
next
  case (Suc sz)
  then show ?case
    by (auto simp: get_mem_bytes_def Let_def
             intro!: map_option_cong map_cong foldl_cong
                     arg_cong[where f = just_list] arg_cong2[where f = and_bit])
qed

lemma get_mem_bytes_tagged_tagstate:
  assumes "get_mem_bytes addr sz s = Some (v, B1)"
  shows "\<forall>addr' \<in> {addr..<addr + sz}. tagstate s addr' = Some B1"
  using assms
  by (auto simp: get_mem_bytes_def foldl_and_bit_eq_iff Let_def split: option.splits)

end
*)
