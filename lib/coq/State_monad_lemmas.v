(*==========================================================================*)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(*==========================================================================*)

Require Import Sail.State_monad.
(*Require Import Sail.Values_lemmas.*)
Require Export Setoid.
Require Export Morphisms Equivalence.

(* Basic results for reasoning about definitions which use the state monad.

   Note that rewriting results are put into both a rewriting hint database and
   a normal automation one.  The former can be used with autorewrite and friends,
   but the latter can be used with the rewriting under congruence tactics, such as
   statecong in Sail.State_lemmas, and PrePostE_rewrite in Hoare. *)

(* Ensure that pointwise equality on states is the preferred notion of
   equivalence for the state monad. *)
Local Open Scope equiv_scope.
#[export] Instance monadS_equivalence {Regs A E} :
  Equivalence (pointwise_relation (sequential_state Regs) (pointwise_relation ChoiceSource (@eq (list (result A E * sequential_state Regs * ChoiceSource))))) | 9.
split; apply _.
Qed.

#[export] Instance refl_eq_subrelation {A : Type} {R : A -> A -> Prop} `{Reflexive A R} : subrelation eq R.
intros x y EQ. subst. reflexivity.
Qed.

#[export] Hint Extern 4 (_ === _) => reflexivity : core.
#[export] Hint Extern 4 (_ === _) => symmetry : core.



Lemma bindS_ext_cong (*[fundef_cong]:*) {Regs A B E}
  {m1 m2 : monadS Regs A E} {f1 f2 : A -> monadS Regs B E} s cs :
  m1 s cs = m2 s cs ->
  (forall a s' cs', List.In (Value a, s', cs') (m2 s cs) -> f1 a s' cs' = f2 a s' cs') ->
  bindS m1 f1 s cs = bindS m2 f2 s cs.
intros.
unfold bindS.
rewrite H.
rewrite !List.flat_map_concat_map.
f_equal.
apply List.map_ext_in.
intros [[[a|a] s'] cs'] H_in; auto.
Qed.

(* Weaker than the Isabelle version, but avoids talking about individual states *)
Lemma bindS_cong (*[fundef_cong]:*) Regs A B E m1 m2 (f1 f2 : A -> monadS Regs B E) :
  m1 === m2 ->
  (forall a, f1 a === f2 a) ->
  bindS m1 f1 === bindS m2 f2.
intros M F s cs.
apply bindS_ext_cong; intros; auto.
apply M.
apply F.
Qed.

Add Parametric Morphism {Regs A B E : Type} : (@bindS Regs A B E)
  with signature equiv ==> equiv ==> equiv as bindS_morphism.
auto using bindS_cong.
Qed.

Lemma bindS_returnS_left Regs A B E {x : A} {f : A -> monadS Regs B E} :
 bindS (returnS x) f === f x.
intros s cs.
unfold returnS, bindS.
simpl.
auto using List.app_nil_r.
Qed.
#[export] Hint Rewrite bindS_returnS_left : state.
#[export] Hint Resolve bindS_returnS_left : state.

Lemma bindS_returnS_right Regs A E {m : monadS Regs A E} :
 bindS m returnS === m.
intros s cs.
unfold returnS, bindS.
induction (m s cs) as [|[[[a|a] s'] cs'] t]; auto;
simpl;
rewrite IHt;
reflexivity.
Qed.
#[export] Hint Rewrite bindS_returnS_right : state.
#[export] Hint Resolve bindS_returnS_right : state.

Lemma bindS_readS {Regs A E} {f} {m : A -> monadS Regs A E} {s cs} :
  bindS (readS f) m s cs = m (f s) s cs.
unfold readS, bindS.
simpl.
rewrite List.app_nil_r.
reflexivity.
Qed.

Lemma bindS_updateS {Regs A E} {f : sequential_state Regs -> sequential_state Regs} {m : unit -> monadS Regs A E} {s cs} :
  bindS (updateS f) m s cs = m tt (f s) cs.
unfold updateS, bindS.
simpl.
auto using List.app_nil_r.
Qed.

Lemma bindS_assertS_true Regs A E msg {f : unit -> monadS Regs A E} :
  bindS (assert_expS true msg) f === f tt.
intros s cs.
unfold assert_expS, bindS.
simpl.
auto using List.app_nil_r.
Qed.
#[export] Hint Rewrite bindS_assertS_true : state.
#[export] Hint Resolve bindS_assertS_true : state.

Lemma bindS_choose_listS_returnS (*[simp]:*) Regs A B E {xs : list A} {f : A -> B} :
  bindS (Regs := Regs) (E := E) (choose_listS xs) (fun x => returnS (f x)) === choose_listS (List.map f xs).
intros s cs.
unfold chooseS, bindS, returnS.
induction xs; auto.
simpl. rewrite IHxs.
reflexivity.
Qed.
#[export] Hint Rewrite bindS_choose_listS_returnS : state.
#[export] Hint Resolve bindS_choose_listS_returnS : state.

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

Lemma bindS_cases {Regs A B E} {m} {f : A -> monadS Regs B E} {r s s' cs cs'} :
  List.In (r, s', cs') (bindS m f s cs) ->
  (exists a a' s'' cs'', r = Value a /\ List.In (Value a', s'', cs'') (m s cs) /\ List.In (Value a, s', cs') (f a' s'' cs'')) \/
  (exists e, r = Ex e /\ List.In (Ex e, s', cs') (m s cs)) \/
  (exists e a s'' cs'', r = Ex e /\ List.In (Value a, s'', cs'') (m s cs) /\ List.In (Ex e, s', cs') (f a s'' cs'')).
unfold bindS.
intro IN.
apply List.in_flat_map in IN.
destruct IN as [[[r' s''] cs''] [INr' INr]].
destruct r' as [a'|e'].
* destruct r as [a|e].
  + left. eauto 10.
  + right; right. eauto 10.
* right; left. simpl in INr. destruct INr as [|[]]. inversion H. subst. eauto 10.
Qed.

Lemma bindS_intro_Value {Regs A B E} {m} {f : A -> monadS Regs B E} {s cs a s' cs' a' s'' cs''} :
 List.In (Value a', s'', cs'') (m s cs) -> List.In (Value a, s', cs') (f a' s'' cs'') -> List.In (Value a, s', cs') (bindS m f s cs).
intros; unfold bindS.
apply List.in_flat_map.
eauto.
Qed.
Lemma bindS_intro_Ex_left {Regs A B E} {m} {f : A -> monadS Regs B E} {s cs e s' cs'} :
  List.In (Ex e, s', cs') (m s cs) -> List.In (Ex e, s', cs') (bindS m f s cs).
intros; unfold bindS.
apply List.in_flat_map.
exists (Ex e, s', cs').
auto with datatypes.
Qed.
Lemma bindS_intro_Ex_right {Regs A B E} {m} {f : A -> monadS Regs B E} {s cs e s' cs' a s'' cs''} :
  List.In (Ex e, s', cs') (f a s'' cs'') -> List.In (Value a, s'', cs'') (m s cs) -> List.In (Ex e, s', cs') (bindS m f s cs).
intros; unfold bindS.
apply List.in_flat_map.
eauto.
Qed.
#[export] Hint Resolve bindS_intro_Value bindS_intro_Ex_left bindS_intro_Ex_right : bindS_intros.

Lemma bindS_assoc Regs A B C E {m} {f : A -> monadS Regs B E} {g : B -> monadS Regs C E} :
  bindS (bindS m f) g === bindS m (fun x => bindS (f x) g).
intros s cs.
unfold bindS.
induction (m s cs) as [ | [[[a | e] t] cs']].
* reflexivity.
* simpl. rewrite <- IHl.
  rewrite !List.flat_map_concat_map.
  rewrite List.map_app.
  rewrite List.concat_app.
  reflexivity.
* simpl. rewrite IHl. reflexivity.
Qed.
#[export] Hint Rewrite bindS_assoc : state.
#[export] Hint Resolve bindS_assoc : state.

Lemma bindS_failS Regs A B E {msg} {f : A -> monadS Regs B E} :
  bindS (failS msg) f = failS msg.
reflexivity.
Qed.
#[export] Hint Rewrite bindS_failS : state.
#[export] Hint Resolve bindS_failS : state.

Lemma bindS_throwS Regs A B E {e} {f : A -> monadS Regs B E} :
  bindS (throwS e) f = throwS e.
reflexivity.
Qed.
#[export] Hint Rewrite bindS_throwS : state.
#[export] Hint Resolve bindS_throwS : state.

(*declare seqS_def[simp]*)
Lemma seqS_def Regs A E m (m' : monadS Regs A E) :
  m >>$ m' = m >>$= (fun _ => m').
reflexivity.
Qed.
#[export] Hint Rewrite seqS_def : state.
#[export] Hint Resolve seqS_def : state.

Lemma Value_bindS_elim {Regs A B E} {a m} {f : A -> monadS Regs B E} {s cs s' cs'} :
  List.In (Value a, s', cs') (bindS m f s cs) ->
  exists s'' cs'' a', List.In (Value a', s'', cs'') (m s cs) /\ List.In (Value a, s', cs') (f a' s'' cs'').
intro H.
apply bindS_cases in H.
destruct H as [(a0 & a' & s'' & cs'' & [= <-] & [*]) | [(e & [= ] & _) | (_ & _ & _ & _ & [= ] & _)]].
eauto.
Qed.

Lemma Ex_bindS_elim {Regs A B E} {e m s cs s' cs'} {f : A -> monadS Regs B E} :
  List.In (Ex e, s', cs') (bindS m f s cs) ->
  List.In (Ex e, s', cs') (m s cs) \/
  exists s'' cs'' a', List.In (Value a', s'', cs'') (m s cs) /\ List.In (Ex e, s', cs') (f a' s'' cs'').
intro H.
apply bindS_cases in H.
destruct H as [(? & ? & ? & ? & [= ] & _) | [(? & [= <-] & X) | (? & ? & ? & ? & [= <-] & X)]];
eauto.
Qed.

Lemma try_catchS_returnS Regs A E1 E2 {a} {h : E1 -> monadS Regs A E2}:
  try_catchS (returnS a) h = returnS a.
reflexivity.
Qed.
#[export] Hint Rewrite try_catchS_returnS : state.
#[export] Hint Resolve try_catchS_returnS : state.
Lemma try_catchS_failS Regs A E1 E2 {msg} {h : E1 -> monadS Regs A E2}:
  try_catchS (failS msg) h = failS msg.
reflexivity.
Qed.
#[export] Hint Rewrite try_catchS_failS : state.
#[export] Hint Resolve try_catchS_failS : state.
Lemma try_catchS_throwS Regs A E1 E2 {e} {h : E1 -> monadS Regs A E2}:
  try_catchS (throwS e) h === h e.
intros s cs.
unfold try_catchS, throwS.
simpl.
auto using List.app_nil_r.
Qed.
#[export] Hint Rewrite try_catchS_throwS : state.
#[export] Hint Resolve try_catchS_throwS : state.

Lemma try_catchS_cong (*[cong]:*) {Regs A E1 E2 m1 m2} {h1 h2 : E1 -> monadS Regs A E2} :
  m1 === m2 ->
  (forall e, h1 e === h2 e) ->
  try_catchS m1 h1 === try_catchS m2 h2.
intros H1 H2 s cs.
unfold try_catchS.
rewrite H1.
rewrite !List.flat_map_concat_map.
f_equal.
apply List.map_ext_in.
intros [[[a|[e|msg]] s'] cs'] H_in; auto. apply H2.
Qed.

Add Parametric Morphism {Regs A E1 E2 : Type} : (@try_catchS Regs A E1 E2)
  with signature equiv ==> equiv ==> equiv as try_catchS_morphism.
intros. auto using try_catchS_cong.
Qed.

Add Parametric Morphism {Regs A E : Type} : (@catch_early_returnS Regs A E)
  with signature equiv ==> equiv as catch_early_returnS_morphism.
intros.
unfold catch_early_returnS.
rewrite H.
reflexivity.
Qed.

Lemma try_catchS_cases {Regs A E1 E2 m} {h : E1 -> monadS Regs A E2} {r s cs s' cs'} :
  List.In (r, s', cs') (try_catchS m h s cs) ->
  (exists a, r = Value a /\ List.In (Value a, s', cs') (m s cs)) \/
  (exists msg, r = Ex (Failure msg) /\ List.In (Ex (Failure msg), s', cs') (m s cs)) \/
  (exists e s'' cs'', List.In (Ex (Throw e), s'', cs'') (m s cs) /\ List.In (r, s', cs') (h e s'' cs'')).
unfold try_catchS.
intro IN.
apply List.in_flat_map in IN.
destruct IN as [[[r' s''] cs''] [INr' INr]].
destruct r' as [a'|[e'|msg]].
* left. simpl in INr. destruct INr as [[= <- <- <-] | []]. eauto 10.
* simpl in INr. destruct INr as [[= <- <- <-] | []]. eauto 10.
* eauto 10.
Qed.

Lemma try_catchS_intros {Regs A E1 E2} {m} {h : E1 -> monadS Regs A E2} :
  (forall s cs a s' cs', List.In (Value a, s', cs') (m s cs) -> List.In (Value a, s', cs') (try_catchS m h s cs)) /\
  (forall s cs msg s' cs', List.In (Ex (Failure msg), s', cs') (m s cs) -> List.In (Ex (Failure msg), s', cs') (try_catchS m h s cs)) /\
  (forall s cs e s'' cs'' r s' cs', List.In (Ex (Throw e), s'', cs'') (m s cs) -> List.In (r, s', cs') (h e s'' cs'') -> List.In (r, s', cs') (try_catchS m h s cs)).
repeat split; unfold try_catchS; intros;
apply List.in_flat_map.
* eexists; split; [ apply H | ]. simpl. auto.
* eexists; split; [ apply H | ]. simpl. auto.
* eexists; split; [ apply H | ]. simpl. auto.
Qed.

Lemma no_Ex_basic_builtins (*[simp]:*) {Regs E} {s s' : sequential_state Regs} {cs cs'} {e : ex E} :
  (forall A (a:A), ~ List.In (Ex e, s', cs') (returnS a s cs)) /\
  (forall A (f : _ -> A), ~ List.In (Ex e, s', cs') (readS f s cs)) /\
  (forall f, ~ List.In (Ex e, s', cs') (updateS f s cs)) /\
  (forall A (xs : list A), ~ List.In (Ex e, s', cs') (choose_listS xs s cs)).
repeat split; intros;
unfold returnS, readS, updateS, chooseS; simpl;
try intuition congruence.
* intro H.
  apply List.in_map_iff in H.
  destruct H as [x [X _]].
  congruence.
Qed.

Import List.ListNotations.
Definition ignore_throw_aux {A E1 E2 S CS} (rs : result A E1 * S * CS) : list (result A E2 * S * CS) :=
match rs with
| (Value a, s', cs') => [(Value a, s', cs')]
| (Ex (Throw e), s', cs') => []
| (Ex (Failure msg), s', cs') => [(Ex (Failure msg), s', cs')]
end.
Definition ignore_throw {A E1 E2 S CS} (m : S -> CS -> list (result A E1 * S * CS)) s cs : list (result A E2 * S * CS) :=
 List.flat_map ignore_throw_aux (m s cs).

Lemma ignore_throw_cong {Regs A E1 E2} {m1 m2 : monadS Regs A E1} :
  m1 === m2 ->
  ignore_throw (E2 := E2) m1 === ignore_throw m2.
intros H s cs.
unfold ignore_throw.
rewrite H.
reflexivity.
Qed.

Lemma ignore_throw_aux_member_simps (*[simp]:*) {A E1 E2 S CS} {s' : S} (cs' : CS) {ms} :
  (forall a:A, List.In (Value a, s', cs') (ignore_throw_aux (E1 := E1) (E2 := E2) ms) <-> ms = (Value a, s', cs')) /\
  (forall e, ~ List.In (Ex (E := E2) (Throw e), s', cs') (ignore_throw_aux ms)) /\
  (forall msg, List.In (Ex (E := E2) (Failure msg), s', cs') (ignore_throw_aux ms) <-> ms = (Ex (Failure msg), s', cs')).
destruct ms as [[[a' | [e' | msg']] s] cs]; simpl;
intuition congruence.
Qed.

Lemma ignore_throw_member_simps (*[simp]:*) {A E1 E2 S CS} {s s' : S} (cs cs' : CS) {m} :
  (forall {a:A}, List.In (Value (E := E2) a, s', cs') (ignore_throw m s cs) <-> List.In (Value (E := E1) a, s', cs') (m s cs)) /\
  (forall {a:A}, List.In (Value (E := E2) a, s', cs') (ignore_throw m s cs) <-> List.In (Value a, s', cs') (m s cs)) /\
  (forall e, ~ List.In (Ex (E := E2) (Throw e), s', cs') (ignore_throw m s cs)) /\
  (forall {msg}, List.In (Ex (E := E2) (Failure msg), s', cs') (ignore_throw m s cs) <-> List.In (Ex (Failure msg), s', cs') (m s cs)).
unfold ignore_throw.
repeat apply conj; intros; try apply conj;
rewrite ?List.in_flat_map;
solve
[ intros [x [H1 H2]]; apply ignore_throw_aux_member_simps in H2; congruence
| intro H; eexists; split; [ apply H | apply ignore_throw_aux_member_simps; reflexivity] ].
Qed.

Lemma ignore_throw_cases {A E S CS} {m : S -> CS -> list (result A E * S * CS)} {r s cs s' cs'} :
  ignore_throw m s cs = m s cs ->
  List.In (r, s', cs') (m s cs) ->
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

Lemma ignore_throw_bindS (*[simp]:*) Regs A B E E2 {m} {f : A -> monadS Regs B E} :
  ignore_throw (E2 := E2) (bindS m f) === bindS (ignore_throw m) (fun s => ignore_throw (f s)).
intros s cs.
unfold bindS, ignore_throw.
induction (m s cs) as [ | [[[a | [e | msg]] t] cs']].
* reflexivity.
* simpl. rewrite <- IHl. rewrite flat_map_app. reflexivity.
* simpl. rewrite <- IHl. reflexivity.
* simpl. apply IHl.
Qed.
#[export] Hint Rewrite ignore_throw_bindS : ignore_throw.
#[export] Hint Resolve ignore_throw_bindS : ignore_throw.

Lemma try_catchS_bindS_no_throw {Regs A B E1 E2} {m1 : monadS Regs A E1} {m2 : monadS Regs A E2} {f : A -> monadS Regs B _} {h} :
  ignore_throw m1 === m1 ->
  ignore_throw m1 === m2 ->
  try_catchS (bindS m1 f) h === bindS m2 (fun a => try_catchS (f a) h).
intros Ignore1 Ignore2.
transitivity ((ignore_throw m1 >>$= (fun a => try_catchS (f a) h))).
* intros s cs.
  unfold bindS, try_catchS, ignore_throw.
  specialize (Ignore1 s cs). revert Ignore1. unfold ignore_throw.
  induction (m1 s cs) as [ | [[[a | [e | msg]] t] cs']]; auto.
  + intro Ig. simpl. rewrite flat_map_app. rewrite IHl. auto. injection Ig. auto.
  + intro Ig. simpl. rewrite IHl. reflexivity. injection Ig. auto.
  + intro Ig. exfalso. clear -Ig.
    assert (List.In (Ex (Throw msg), t, cs') (List.flat_map ignore_throw_aux l)).
    simpl in Ig. rewrite Ig. simpl. auto.
    apply List.in_flat_map in H.
    destruct H as [x [H1 H2]].
    apply ignore_throw_aux_member_simps in H2.
    assumption.
* apply bindS_cong; auto.
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
Lemma no_throw_basic_builtins_4 Regs A E1 E2 {xs : list A} :
  ignore_throw (E1 := E1) (choose_listS xs) === @choose_listS Regs A E2 xs.
intros s cs.
unfold ignore_throw, choose_listS.
rewrite List.flat_map_concat_map, List.map_map. simpl.
rewrite concat_map_singleton.
reflexivity.
Qed.
Lemma no_throw_basic_builtins_5 Regs E1 E2 ty :
  ignore_throw (E1 := E1) (chooseS ty) === @chooseS Regs E2 ty.
intros s cs.
unfold ignore_throw, chooseS.
destruct (choose cs ty); reflexivity.
Qed.
Lemma no_throw_basic_builtins_6 Regs A E1 E2 msg :
  ignore_throw (E1 := E1) (failS msg) = @failS Regs A E2 msg.
reflexivity. Qed.
Lemma no_throw_basic_builtins_7 Regs A E1 E2 msg x :
  ignore_throw (E1 := E1) (maybe_failS msg x) = @maybe_failS Regs A E2 msg x. 
destruct x; reflexivity. Qed.

#[export] Hint Rewrite no_throw_basic_builtins_1 no_throw_basic_builtins_2
             no_throw_basic_builtins_3 no_throw_basic_builtins_4
             no_throw_basic_builtins_5 no_throw_basic_builtins_6
             no_throw_basic_builtins_7 : ignore_throw.
#[export] Hint Resolve no_throw_basic_builtins_1 no_throw_basic_builtins_2
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

Lemma no_throw_mem_builtins_1 Regs E1 E2 rk a sz :
  ignore_throw (E2 := E2) (@read_memt_bytesS Regs E1 rk a sz) === read_memt_bytesS rk a sz.
unfold read_memt_bytesS. autorewrite with ignore_throw.
apply bindS_cong; auto. intros.  autorewrite with ignore_throw. reflexivity.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_1 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_1 : ignore_throw.
Lemma no_throw_mem_builtins_2 Regs E1 E2 rk a sz :
  ignore_throw (E2 := E2) (@read_mem_bytesS Regs E1 rk a sz) === read_mem_bytesS rk a sz.
unfold read_mem_bytesS. autorewrite with ignore_throw.
apply bindS_cong; intros; autorewrite with ignore_throw; auto.
destruct a0; reflexivity.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_2 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_2 : ignore_throw.
Lemma no_throw_mem_builtins_3 Regs A E1 E2 a :
  ignore_throw (E2 := E2) (@read_tagS Regs A E1 a) === read_tagS a.
reflexivity. Qed.
#[export] Hint Rewrite no_throw_mem_builtins_3 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_3 : ignore_throw.
Lemma no_throw_mem_builtins_4 Regs A E1 E2 rk a sz :
  ignore_throw (E2 := E2) (@read_memtS Regs E1 A rk a sz) === read_memtS rk a sz.
unfold read_memtS. autorewrite with ignore_throw.
apply bindS_cong; intros; autorewrite with ignore_throw.
reflexivity. destruct a0; simpl. autorewrite with ignore_throw.
reflexivity.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_4 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_4 : ignore_throw.
Lemma no_throw_mem_builtins_5 Regs A E1 E2 rk a sz :
  ignore_throw (E2 := E2) (@read_memS Regs E1 A rk a sz) === read_memS rk a sz.
unfold read_memS. autorewrite with ignore_throw.
apply bindS_cong; intros; autorewrite with ignore_throw; auto.
destruct a0; auto.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_5 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_5 : ignore_throw.
Lemma no_throw_mem_builtins_6 Regs E1 E2 wk addr sz v t :
  ignore_throw (E2 := E2) (@write_memt_bytesS Regs E1 wk addr sz v t) === write_memt_bytesS wk addr sz v t.
unfold write_memt_bytesS. unfold seqS. autorewrite with ignore_throw.
reflexivity.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_6 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_6 : ignore_throw.
Lemma no_throw_mem_builtins_7 Regs E1 E2 wk addr sz v :
  ignore_throw (E2 := E2) (@write_mem_bytesS Regs E1 wk addr sz v) === write_mem_bytesS wk addr sz v.
unfold write_mem_bytesS. autorewrite with ignore_throw. reflexivity.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_7 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_7 : ignore_throw.
Lemma no_throw_mem_builtins_8 Regs E1 E2 A wk addr sz v t :
  ignore_throw (E2 := E2) (@write_memtS Regs E1 A wk addr sz v t) === write_memtS wk addr sz v t.
unfold write_memtS. rewrite ignore_throw_option_case_distrib_2.
destruct (Sail.Values.mem_bytes_of_bits v); autorewrite with ignore_throw; auto.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_8 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_8 : ignore_throw.
Lemma no_throw_mem_builtins_9 Regs E1 E2 A wk addr sz v :
  ignore_throw (E2 := E2) (@write_memS Regs E1 A wk addr sz v) === write_memS wk addr sz v.
unfold write_memS. autorewrite with ignore_throw; auto.
Qed.
#[export] Hint Rewrite no_throw_mem_builtins_9 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_9 : ignore_throw.
Lemma no_throw_mem_builtins_10 Regs E1 E2 :
  ignore_throw (E2 := E2) (@excl_resultS Regs E1 tt) === excl_resultS tt.
reflexivity. Qed.
#[export] Hint Rewrite no_throw_mem_builtins_10 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_10 : ignore_throw.
(*
Lemma no_throw_mem_builtins_11 Regs E1 E2 :
  ignore_throw (E2 := E2) (@undefined_boolS Regs E1 tt) === undefined_boolS tt.
reflexivity. Qed.
#[export] Hint Rewrite no_throw_mem_builtins_11 : ignore_throw.
#[export] Hint Resolve no_throw_mem_builtins_11 : ignore_throw.
*)
Lemma no_throw_read_regvalS Regs RV E1 E2 r reg_name :
  ignore_throw (E2 := E2) (@read_regvalS Regs RV E1 r reg_name) === read_regvalS r reg_name.
destruct r; simpl. autorewrite with ignore_throw.
apply bindS_cong; intros; auto. rewrite ignore_throw_option_case_distrib_2.
autorewrite with ignore_throw. reflexivity.
Qed.
#[export] Hint Rewrite no_throw_read_regvalS : ignore_throw.
#[export] Hint Resolve no_throw_read_regvalS : ignore_throw.

Lemma no_throw_write_regvalS Regs RV E1 E2 r reg_name v :
  ignore_throw (E2 := E2) (@write_regvalS Regs RV E1 r reg_name v) === write_regvalS r reg_name v.
destruct r; simpl. autorewrite with ignore_throw.
apply bindS_cong; intros; auto. rewrite ignore_throw_option_case_distrib_2.
autorewrite with ignore_throw. reflexivity.
Qed.
#[export] Hint Rewrite no_throw_write_regvalS : ignore_throw.
#[export] Hint Resolve no_throw_write_regvalS : ignore_throw.

