Require Import Sail2_state_monad.
(*Require Import Sail2_values_lemmas.*)

Lemma bindS_ext_cong (*[fundef_cong]:*) {Regs A B E}
  {m1 m2 : monadS Regs A E} {f1 f2 : A -> monadS Regs B E} s :
  m1 s = m2 s ->
  (forall a s', List.In (Value a, s') (m2 s) -> f1 a s' = f2 a s') ->
  bindS m1 f1 s = bindS m2 f2 s.
intros.
unfold bindS.
rewrite H.
rewrite !List.flat_map_concat_map.
f_equal.
apply List.map_ext_in.
intros [[a|a] s'] H_in; auto.
Qed.

(*
lemma bindS_cong[fundef_cong]:
  assumes m: "m1 = m2"
    and f: "\<And>s a s'. (Value a, s') \<in> (m2 s) \<Longrightarrow> f1 a s' = f2 a s'"
  shows "bindS m1 f1 = bindS m2 f2"
  using assms by (intro ext bindS_ext_cong; blast)
*)

Lemma bindS_returnS_left (*[simp]:*) {Regs A B E} {x : A} {f : A -> monadS Regs B E} {s} :
 bindS (returnS x) f s = f x s.
unfold returnS, bindS.
simpl.
auto using List.app_nil_r.
Qed.

Lemma bindS_returnS_right (*[simp]:*) {Regs A E} {m : monadS Regs A E} {s} :
 bindS m returnS s = m s.
unfold returnS, bindS.
induction (m s) as [|[[a|a] s'] t]; auto;
simpl;
rewrite IHt;
reflexivity.
Qed.

Lemma bindS_readS {Regs A E} {f} {m : A -> monadS Regs A E} {s} :
  bindS (readS f) m s = m (f s) s.
unfold readS, bindS.
simpl.
rewrite List.app_nil_r.
reflexivity.
Qed.

Lemma bindS_updateS {Regs A E} {f : sequential_state Regs -> sequential_state Regs} {m : unit -> monadS Regs A E} {s} :
  bindS (updateS f) m s = m tt (f s).
unfold updateS, bindS.
simpl.
auto using List.app_nil_r.
Qed.

Lemma bindS_assertS_True (*[simp]:*) {Regs A E msg} {f : unit -> monadS Regs A E} {s} :
  bindS (assert_expS true msg) f s = f tt s.
unfold assert_expS, bindS.
simpl.
auto using List.app_nil_r.
Qed.

Lemma bindS_chooseS_returnS (*[simp]:*) {Regs A B E} {xs : list A} {f : A -> B} {s} :
  bindS (Regs := Regs) (E := E) (chooseS xs) (fun x => returnS (f x)) s = chooseS (List.map f xs) s.
unfold chooseS, bindS, returnS.
induction xs; auto.
simpl. rewrite IHxs.
reflexivity.
Qed.

Lemma result_cases : forall (A E : Type) (P : result A E -> Prop),
  (forall a, P (Value a)) ->
  (forall e, P (Ex (Throw e))) ->
  (forall msg, P (Ex (Failure msg))) ->
  forall r, P r.
intros.
destruct r; auto.
destruct e; auto.
Qed.

Lemma result_state_cases {A E S} {P : result A E * S -> Prop} :
  (forall a s, P (Value a, s)) ->
  (forall e s, P (Ex (Throw e), s)) ->
  (forall msg s, P (Ex (Failure msg), s)) ->
  forall rs, P rs.
intros.
destruct rs as [[a|[e|msg]] s]; auto.
Qed.

(* TODO: needs sets, not lists
Lemma monadS_ext_eqI {Regs A E} {m m' : monadS Regs A E} s :
  (forall a s', List.In (Value a, s') (m s) <-> List.In (Value a, s') (m' s)) ->
  (forall e s', List.In (Ex (Throw e), s') (m s) <-> List.In (Ex (Throw e), s') (m' s)) ->
  (forall msg s', List.In (Ex (Failure msg), s') (m s) <-> List.In (Ex (Failure msg), s') (m' s)) ->
  m s = m' s.
proof (intro set_eqI)
  fix x
  show "x \<in> m s \<longleftrightarrow> x \<in> m' s" using assms by (cases x rule: result_state_cases) auto
qed

lemma monadS_eqI:
  fixes m m' :: "('regs, 'a, 'e) monadS"
  assumes "\<And>s a s'. (Value a, s') \<in> m s \<longleftrightarrow> (Value a, s') \<in> m' s"
    and "\<And>s e s'. (Ex (Throw e), s') \<in> m s \<longleftrightarrow> (Ex (Throw e), s') \<in> m' s"
    and "\<And>s msg s'. (Ex (Failure msg), s') \<in> m s \<longleftrightarrow> (Ex (Failure msg), s') \<in> m' s"
  shows "m = m'"
  using assms by (intro ext monadS_ext_eqI)
*)

Lemma bindS_cases {Regs A B E} {m} {f : A -> monadS Regs B E} {r s s'} :
  List.In (r, s') (bindS m f s) ->
  (exists a a' s'', r = Value a /\ List.In (Value a', s'') (m s) /\ List.In (Value a, s') (f a' s'')) \/
  (exists e, r = Ex e /\ List.In (Ex e, s') (m s)) \/
  (exists e a s'', r = Ex e /\ List.In (Value a, s'') (m s) /\ List.In (Ex e, s') (f a s'')).
unfold bindS.
intro IN.
apply List.in_flat_map in IN.
destruct IN as [[r' s''] [INr' INr]].
destruct r' as [a'|e'].
* destruct r as [a|e].
  + left. eauto 10.
  + right; right. eauto 10.
* right; left. simpl in INr. destruct INr as [|[]]. inversion H. subst. eauto 10.
Qed.

Lemma bindS_intro_Value {Regs A B E} {m} {f : A -> monadS Regs B E} {s a s' a' s''} :
 List.In (Value a', s'') (m s) -> List.In (Value a, s') (f a' s'') -> List.In (Value a, s') (bindS m f s).
intros; unfold bindS.
apply List.in_flat_map.
eauto.
Qed.
Lemma bindS_intro_Ex_left {Regs A B E} {m} {f : A -> monadS Regs B E} {s e s'} :
  List.In (Ex e, s') (m s) -> List.In (Ex e, s') (bindS m f s).
intros; unfold bindS.
apply List.in_flat_map.
exists (Ex e, s').
auto with datatypes.
Qed.
Lemma bindS_intro_Ex_right {Regs A B E} {m} {f : A -> monadS Regs B E} {s e s' a s''} :
  List.In (Ex e, s') (f a s'') -> List.In (Value a, s'') (m s) -> List.In (Ex e, s') (bindS m f s).
intros; unfold bindS.
apply List.in_flat_map.
eauto.
Qed.
Hint Resolve bindS_intro_Value bindS_intro_Ex_left bindS_intro_Ex_right : bindS_intros.

Lemma bindS_assoc (*[simp]:*) {Regs A B C E} {m} {f : A -> monadS Regs B E} {g : B -> monadS Regs C E} {s} :
  bindS (bindS m f) g s = bindS m (fun x => bindS (f x) g) s.
unfold bindS.
induction (m s) as [ | [[a | e] t]].
* reflexivity.
* simpl. rewrite <- IHl.
  rewrite !List.flat_map_concat_map.
  rewrite List.map_app.
  rewrite List.concat_app.
  reflexivity.
* simpl. rewrite IHl. reflexivity.
Qed.

Lemma bindS_failS (*[simp]:*) {Regs A B E} {msg} {f : A -> monadS Regs B E} :
  bindS (failS msg) f = failS msg.
reflexivity.
Qed.
Lemma bindS_throwS (*[simp]:*) {Regs A B E} {e} {f : A -> monadS Regs B E} :
  bindS (throwS e) f = throwS e.
reflexivity.
Qed.
(*declare seqS_def[simp]*)

Lemma Value_bindS_elim {Regs A B E} {a m} {f : A -> monadS Regs B E} {s s'} :
  List.In (Value a, s') (bindS m f s) ->
  exists s'' a', List.In (Value a', s'') (m s) /\ List.In (Value a, s') (f a' s'').
intro H.
apply bindS_cases in H.
destruct H as [(a0 & a' & s'' & [= <-] & [*]) | [(e & [= ] & _) | (_ & _ & _ & [= ] & _)]].
eauto.
Qed.

Lemma Ex_bindS_elim {Regs A B E} {e m s s'} {f : A -> monadS Regs B E} :
  List.In (Ex e, s') (bindS m f s) ->
  List.In (Ex e, s') (m s) \/
  exists s'' a', List.In (Value a', s'') (m s) /\ List.In (Ex e, s') (f a' s'').
intro H.
apply bindS_cases in H.
destruct H as [(? & ? & ? & [= ] & _) | [(? & [= <-] & X) | (? & ? & ? & [= <-] & X)]];
eauto.
Qed.

Lemma try_catchS_returnS (*[simp]:*) {Regs A E1 E2} {a} {h : E1 -> monadS Regs A E2}:
  try_catchS (returnS a) h = returnS a.
reflexivity.
Qed.
Lemma try_catchS_failS (*[simp]:*) {Regs A E1 E2} {msg} {h : E1 -> monadS Regs A E2}:
  try_catchS (failS msg) h = failS msg.
reflexivity.
Qed.
Lemma try_catchS_throwS (*[simp]:*) {Regs A E1 E2} {e} {h : E1 -> monadS Regs A E2} {s}:
  try_catchS (throwS e) h s = h e s.
unfold try_catchS, throwS.
simpl.
auto using List.app_nil_r.
Qed.

Lemma try_catchS_cong (*[cong]:*) {Regs A E1 E2 m1 m2} {h1 h2 : E1 -> monadS Regs A E2} {s} :
  (forall s, m1 s = m2 s) ->
  (forall e s, h1 e s = h2 e s) ->
  try_catchS m1 h1 s = try_catchS m2 h2 s.
intros H1 H2.
unfold try_catchS.
rewrite H1.
rewrite !List.flat_map_concat_map.
f_equal.
apply List.map_ext_in.
intros [[a|[e|msg]] s'] H_in; auto.
Qed.

Lemma try_catchS_cases {Regs A E1 E2 m} {h : E1 -> monadS Regs A E2} {r s s'} :
  List.In (r, s') (try_catchS m h s) ->
  (exists a, r = Value a /\ List.In (Value a, s') (m s)) \/
  (exists msg, r = Ex (Failure msg) /\ List.In (Ex (Failure msg), s') (m s)) \/
  (exists e s'', List.In (Ex (Throw e), s'') (m s) /\ List.In (r, s') (h e s'')).
unfold try_catchS.
intro IN.
apply List.in_flat_map in IN.
destruct IN as [[r' s''] [INr' INr]].
destruct r' as [a'|[e'|msg]].
* left. simpl in INr. destruct INr as [[= <- <-] | []]. eauto 10.
* simpl in INr. destruct INr as [[= <- <-] | []]. eauto 10.
* eauto 10.
Qed.

Lemma try_catchS_intros {Regs A E1 E2} {m} {h : E1 -> monadS Regs A E2} :
  (forall s a s', List.In (Value a, s') (m s) -> List.In (Value a, s') (try_catchS m h s)) /\
  (forall s msg s', List.In (Ex (Failure msg), s') (m s) -> List.In (Ex (Failure msg), s') (try_catchS m h s)) /\
  (forall s e s'' r s', List.In (Ex (Throw e), s'') (m s) -> List.In (r, s') (h e s'') -> List.In (r, s') (try_catchS m h s)).
repeat split; unfold try_catchS; intros;
apply List.in_flat_map.
* eexists; split; [ apply H | ]. simpl. auto.
* eexists; split; [ apply H | ]. simpl. auto.
* eexists; split; [ apply H | ]. simpl. auto.
Qed.

Lemma no_Ex_basic_builtins (*[simp]:*) {Regs E} {s s' : sequential_state Regs} {e : ex E} :
  (forall A (a:A), ~ List.In (Ex e, s') (returnS a s)) /\
  (forall A (f : _ -> A), ~ List.In (Ex e, s') (readS f s)) /\
  (forall f, ~ List.In (Ex e, s') (updateS f s)) /\
  (forall A (xs : list A), ~ List.In (Ex e, s') (chooseS xs s)).
repeat split; intros;
unfold returnS, readS, updateS, chooseS; simpl;
try intuition congruence.
* intro H.
  apply List.in_map_iff in H.
  destruct H as [x [X _]].
  congruence.
Qed.

Import List.ListNotations.
Definition ignore_throw_aux {A E1 E2 S} (rs : result A E1 * S) : list (result A E2 * S) :=
match rs with
| (Value a, s') => [(Value a, s')]
| (Ex (Throw e), s') => []
| (Ex (Failure msg), s') => [(Ex (Failure msg), s')]
end.
Definition ignore_throw {A E1 E2 S} (m : S -> list (result A E1 * S)) s : list (result A E2 * S) :=
 List.flat_map ignore_throw_aux (m s).

Lemma ignore_throw_cong {A E1 E2 S} {m1 m2 : S -> list (result A E1 * S)} s :
  (forall s, m1 s = m2 s) ->
  ignore_throw (E2 := E2) m1 s = ignore_throw m2 s.
intro H.
unfold ignore_throw.
rewrite H.
reflexivity.
Qed.

Lemma ignore_throw_aux_member_simps (*[simp]:*) {A E1 E2 S} {s' : S} {ms} :
  (forall a:A, List.In (Value a, s') (ignore_throw_aux (E1 := E1) (E2 := E2) ms) <-> ms = (Value a, s')) /\
  (forall e, ~ List.In (Ex (E := E2) (Throw e), s') (ignore_throw_aux ms)) /\
  (forall msg, List.In (Ex (E := E2) (Failure msg), s') (ignore_throw_aux ms) <-> ms = (Ex (Failure msg), s')).
destruct ms as [[a' | [e' | msg']] s]; simpl;
intuition congruence.
Qed.

Lemma ignore_throw_member_simps (*[simp]:*) {A E1 E2 S} {s s' : S} {m} :
  (forall {a:A}, List.In (Value (E := E2) a, s') (ignore_throw m s) <-> List.In (Value (E := E1) a, s') (m s)) /\
  (forall {a:A}, List.In (Value (E := E2) a, s') (ignore_throw m s) <-> List.In (Value a, s') (m s)) /\
  (forall e, ~ List.In (Ex (E := E2) (Throw e), s') (ignore_throw m s)) /\
  (forall {msg}, List.In (Ex (E := E2) (Failure msg), s') (ignore_throw m s) <-> List.In (Ex (Failure msg), s') (m s)).
unfold ignore_throw.
repeat apply conj; intros; try apply conj;
rewrite ?List.in_flat_map;
solve
[ intros [x [H1 H2]]; apply ignore_throw_aux_member_simps in H2; congruence
| intro H; eexists; split; [ apply H | apply ignore_throw_aux_member_simps; reflexivity] ].
Qed.

Lemma ignore_throw_cases {A E S} {m : S -> list (result A E * S)} {r s s'} :
  ignore_throw m s = m s ->
  List.In (r, s') (m s) ->
  (exists a, r = Value a) \/
  (exists msg, r = Ex (Failure msg)).
destruct r as [a | [e | msg]]; eauto.
* intros H1 H2. rewrite <- H1 in H2.
  apply ignore_throw_member_simps in H2.
  destruct H2.
Qed.

(* *** *)
Lemma flat_map_app {A B} {f : A -> list B} {l1 l2} :
  List.flat_map f (l1 ++ l2) = (List.flat_map f l1 ++ List.flat_map f l2)%list.
rewrite !List.flat_map_concat_map.
rewrite List.map_app, List.concat_app.
reflexivity.
Qed.

Lemma ignore_throw_bindS (*[simp]:*) Regs A B E E2 {m} {f : A -> monadS Regs B E} {s} :
  ignore_throw (E2 := E2) (bindS m f) s = bindS (ignore_throw m) (fun s => ignore_throw (f s)) s.
unfold bindS, ignore_throw.
induction (m s) as [ | [[a | [e | msg]] t]].
* reflexivity.
* simpl. rewrite <- IHl. rewrite flat_map_app. reflexivity.
* simpl. rewrite <- IHl. reflexivity.
* simpl. apply IHl.
Qed.
Hint Rewrite ignore_throw_bindS : ignore_throw.

Lemma try_catchS_bindS_no_throw {Regs A B E1 E2} {m1 : monadS Regs A E1} {m2 : monadS Regs A E2} {f : A -> monadS Regs B _} {s h} :
  (forall s, ignore_throw m1 s = m1 s) ->
  (forall s, ignore_throw m1 s = m2 s) ->
  try_catchS (bindS m1 f) h s = bindS m2 (fun a => try_catchS (f a) h) s.
intros Ignore1 Ignore2.
transitivity ((ignore_throw m1 >>$= (fun a => try_catchS (f a) h)) s).
* unfold bindS, try_catchS, ignore_throw.
  specialize (Ignore1 s). revert Ignore1. unfold ignore_throw.
  induction (m1 s) as [ | [[a | [e | msg]] t]]; auto.
  + intro Ig. simpl. rewrite flat_map_app. rewrite IHl. auto. injection Ig. auto.
  + intro Ig. simpl. rewrite IHl. reflexivity. injection Ig. auto.
  + intro Ig. exfalso. clear -Ig.
    assert (List.In (Ex (Throw msg), t) (List.flat_map ignore_throw_aux l)).
    simpl in Ig. rewrite Ig. simpl. auto.
    apply List.in_flat_map in H.
    destruct H as [x [H1 H2]].
    apply ignore_throw_aux_member_simps in H2.
    assumption.
* apply bindS_ext_cong; auto.
Qed.

Lemma concat_map_singleton {A B} {f : A -> B} {a : list A} :
  List.concat (List.map (fun x => [f x]%list) a) = List.map f a.
induction a; simpl; try rewrite IHa; auto with datatypes.
Qed.

(*lemma no_throw_basic_builtins[simp]:*)
Lemma no_throw_basic_builtins_1 Regs A E E2 {a : A} :
  ignore_throw (E1 := E2) (returnS a) = @returnS Regs A E a.
reflexivity. Qed.
Lemma no_throw_basic_builtins_2 Regs A E E2 {f : sequential_state Regs -> A} :
  ignore_throw (E1 := E) (E2 := E2) (readS f) = readS f.
reflexivity. Qed.
Lemma no_throw_basic_builtins_3 Regs E E2 {f : sequential_state Regs -> sequential_state Regs} :
  ignore_throw (E1 := E) (E2 := E2) (updateS f) = updateS f.
reflexivity. Qed.
Lemma no_throw_basic_builtins_4 Regs A E1 E2 {xs : list A} s :
  ignore_throw (E1 := E1) (chooseS xs) s = @chooseS Regs A E2 xs s.
unfold ignore_throw, chooseS.
rewrite List.flat_map_concat_map, List.map_map. simpl.
rewrite concat_map_singleton.
reflexivity.
Qed.
Lemma no_throw_basic_builtins_5 Regs E1 E2 :
  ignore_throw (E1 := E1) (choose_boolS tt) = @choose_boolS Regs E2 tt.
reflexivity. Qed.
Lemma no_throw_basic_builtins_6 Regs A E1 E2 msg :
  ignore_throw (E1 := E1) (failS msg) = @failS Regs A E2 msg.
reflexivity. Qed.
Lemma no_throw_basic_builtins_7 Regs A E1 E2 msg x :
  ignore_throw (E1 := E1) (maybe_failS msg x) = @maybe_failS Regs A E2 msg x. 
destruct x; reflexivity. Qed.

Hint Rewrite no_throw_basic_builtins_1 no_throw_basic_builtins_2
             no_throw_basic_builtins_3 no_throw_basic_builtins_4
             no_throw_basic_builtins_5 no_throw_basic_builtins_6
             no_throw_basic_builtins_7 : ignore_throw.

Lemma ignore_throw_option_case_distrib_1 Regs B C E1 E2 (c : sequential_state Regs -> option B) s (n : monadS Regs C E1) (f : B -> monadS Regs C E1) :
  ignore_throw (E2 := E2) (match c s with None => n | Some b => f b end) s =
    match c s with None => ignore_throw n s | Some b => ignore_throw (f b) s end.
destruct (c s); auto.
Qed.
Lemma ignore_throw_option_case_distrib_2 Regs B C E1 E2 (c : option B) (n : monadS Regs C E1) (f : B -> monadS Regs C E1) :
  ignore_throw (E2 := E2) (match c with None => n | Some b => f b end) =
    match c with None => ignore_throw n | Some b => ignore_throw (f b) end.
destruct c; auto.
Qed.

Lemma ignore_throw_let_distrib Regs A B E1 E2 (y : A) (f : A -> monadS Regs B E1) :
  ignore_throw (E2 := E2) (let x := y in f x) = (let x := y in ignore_throw (f x)).
reflexivity.
Qed.

Lemma no_throw_mem_builtins_1 Regs E1 E2 rk a sz s :
  ignore_throw (E2 := E2) (@read_memt_bytesS Regs E1 rk a sz) s = read_memt_bytesS rk a sz s.
unfold read_memt_bytesS. autorewrite with ignore_throw.
apply bindS_ext_cong; auto. intros.  autorewrite with ignore_throw. reflexivity.
Qed.
Hint Rewrite no_throw_mem_builtins_1 : ignore_throw.
Lemma no_throw_mem_builtins_2 Regs E1 E2 rk a sz s :
  ignore_throw (E2 := E2) (@read_mem_bytesS Regs E1 rk a sz) s = read_mem_bytesS rk a sz s.
unfold read_mem_bytesS. autorewrite with ignore_throw.
apply bindS_ext_cong; intros; autorewrite with ignore_throw; auto.
destruct a0; reflexivity.
Qed.
Hint Rewrite no_throw_mem_builtins_2 : ignore_throw.
Lemma no_throw_mem_builtins_3 Regs A E1 E2 a s :
  ignore_throw (E2 := E2) (@read_tagS Regs A E1 a) s = read_tagS a s.
reflexivity. Qed.
Hint Rewrite no_throw_mem_builtins_3 : ignore_throw.
Lemma no_throw_mem_builtins_4 Regs A V E1 E2 rk a sz s H :
  ignore_throw (E2 := E2) (@read_memtS Regs E1 A V rk a sz H) s = read_memtS rk a sz s.
unfold read_memtS. autorewrite with ignore_throw.
apply bindS_ext_cong; intros; autorewrite with ignore_throw.
reflexivity. destruct a0; simpl. autorewrite with ignore_throw.
reflexivity.
Qed.
Hint Rewrite no_throw_mem_builtins_4 : ignore_throw.
Lemma no_throw_mem_builtins_5 Regs A V E1 E2 rk a sz s H :
  ignore_throw (E2 := E2) (@read_memS Regs E1 A V rk a sz H) s = read_memS rk a sz s.
unfold read_memS. autorewrite with ignore_throw.
apply bindS_ext_cong; intros; autorewrite with ignore_throw; auto.
destruct a0; auto.
Qed.
Hint Rewrite no_throw_mem_builtins_5 : ignore_throw.
Lemma no_throw_mem_builtins_6 Regs E1 E2 wk addr sz v t s :
  ignore_throw (E2 := E2) (@write_memt_bytesS Regs E1 wk addr sz v t) s = write_memt_bytesS wk addr sz v t s.
unfold write_memt_bytesS. unfold seqS. autorewrite with ignore_throw.
reflexivity.
Qed.
Hint Rewrite no_throw_mem_builtins_6 : ignore_throw.
Lemma no_throw_mem_builtins_7 Regs E1 E2 wk addr sz v s :
  ignore_throw (E2 := E2) (@write_mem_bytesS Regs E1 wk addr sz v) s = write_mem_bytesS wk addr sz v s.
unfold write_mem_bytesS. autorewrite with ignore_throw. reflexivity.
Qed.
Hint Rewrite no_throw_mem_builtins_7 : ignore_throw.
Lemma no_throw_mem_builtins_8 Regs E1 E2 A B wk addr sz v t s :
  ignore_throw (E2 := E2) (@write_memtS Regs E1 A B wk addr sz v t) s = write_memtS wk addr sz v t s.
unfold write_memtS. rewrite ignore_throw_option_case_distrib_2.
destruct (Sail2_values.mem_bytes_of_bits v); autorewrite with ignore_throw; auto.
Qed.
Hint Rewrite no_throw_mem_builtins_8 : ignore_throw.
Lemma no_throw_mem_builtins_9 Regs E1 E2 A B wk addr sz v s :
  ignore_throw (E2 := E2) (@write_memS Regs E1 A B wk addr sz v) s = write_memS wk addr sz v s.
unfold write_memS. autorewrite with ignore_throw; auto.
Qed.
Hint Rewrite no_throw_mem_builtins_9 : ignore_throw.
Lemma no_throw_mem_builtins_10 Regs E1 E2 s :
  ignore_throw (E2 := E2) (@excl_resultS Regs E1 tt) s = excl_resultS tt s.
reflexivity. Qed.
Hint Rewrite no_throw_mem_builtins_10 : ignore_throw.
Lemma no_throw_mem_builtins_11 Regs E1 E2 s :
  ignore_throw (E2 := E2) (@undefined_boolS Regs E1 tt) s = undefined_boolS tt s.
reflexivity. Qed.
Hint Rewrite no_throw_mem_builtins_11 : ignore_throw.

Lemma no_throw_read_regvalS Regs RV E1 E2 r reg_name s :
  ignore_throw (E2 := E2) (@read_regvalS Regs RV E1 r reg_name) s = read_regvalS r reg_name s.
destruct r; simpl. autorewrite with ignore_throw.
apply bindS_ext_cong; intros; auto. rewrite ignore_throw_option_case_distrib_2.
autorewrite with ignore_throw. reflexivity.
Qed.
Hint Rewrite no_throw_read_regvalS : ignore_throw.

Lemma no_throw_write_regvalS Regs RV E1 E2 r reg_name v s :
  ignore_throw (E2 := E2) (@write_regvalS Regs RV E1 r reg_name v) s = write_regvalS r reg_name v s.
destruct r; simpl. autorewrite with ignore_throw.
apply bindS_ext_cong; intros; auto. rewrite ignore_throw_option_case_distrib_2.
autorewrite with ignore_throw. reflexivity.
Qed.
Hint Rewrite no_throw_write_regvalS : ignore_throw.
