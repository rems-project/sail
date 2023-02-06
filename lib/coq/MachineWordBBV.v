From Sail Require Import TypeCasts.
From Sail Require MachineWordInterface.
From bbv Require Word.
Require Arith.
Require Import ZArith NArith.
Require Lia.
Require String.
Require Strings.Ascii.

Module MachineWord <: MachineWordInterface.MachineWordInterface.

Import List.ListNotations.

Definition dummy {T:Type} (t:T) : T.
exact t.
Qed.

Definition word := Word.word.
Definition zeros n : word n := @Word.wzero n.
Definition ones n : word n := @Word.wones n.
Fixpoint get_bit [n] (w : word n) : nat -> bool :=
  match w with
  | Word.WO => fun i => dummy false
  | Word.WS b w' => fun i =>
             match i with
             | O => b
             | S i' => get_bit w' i'
             end
  end.

Lemma get_bit_eq [n] (w v : word n) :
  (forall i, i < n -> get_bit w i = get_bit v i) -> w = v.
intro H.
induction w.
* rewrite (Word.word0 v).
  reflexivity.
* unfold word in v.
  rewrite (Word.shatter_word v) in *.
  f_equal.
  + apply (H 0).
    Lia.lia.
  + apply IHw.
    intros i LT.
    specialize (H (S i) ltac:(Lia.lia)).
    apply H.
Qed.

(* An alternative definition in the style of set_bit below. *)
Definition get_bit_by_shift [n] : word n -> nat -> bool :=
  match n with
  | O => fun (w : Word.word O) i => dummy false
  | S n => fun (w : Word.word (S n)) i => Word.wlsb (Word.wrshift' w i)
  end.

Lemma combine_bit_low : forall m n (w : word m) (v : word n) i,
  i < m -> get_bit (Word.combine w v) i = get_bit w i.
induction w.
* intros.
  Lia.lia.
* intros v [|i] LT.
  + reflexivity.
  + apply IHw.
    Lia.lia.
Qed.

Lemma combine_bit_high : forall m n (w : word m) (v : word n) i,
  get_bit (Word.combine w v) (i + m) = get_bit v i.
induction w.
* intros.
  simpl.
  rewrite Nat.add_0_r.
  reflexivity.
* intros.
  rewrite Nat.add_succ_r.
  apply IHw.
Qed.

Lemma split2_bit : forall m n w i,
get_bit (Word.split2 m n w) i = get_bit w (i + m).
induction m.
* intros.
  rewrite Nat.add_0_r.
  reflexivity.
* simpl. intros.
  rewrite (Word.shatter_word w) at 2.
  rewrite Nat.add_succ_r.
  apply IHm.
Qed.

Lemma nat_cast_bit : forall m n (w : word m) (H : m = n) i,
  get_bit (DepEqNat.nat_cast Word.word H w) i = get_bit w i.
intros.
subst.
rewrite DepEqNat.nat_cast_same.
reflexivity.
Qed.

Lemma wrshift_bit : forall n (w : word n) i j,
  i + j < n ->
  get_bit (Word.wrshift' w i) j = get_bit w (i + j).
intros.
unfold Word.wrshift'.
rewrite split2_bit.
rewrite nat_cast_bit.
rewrite (Nat.add_comm j i).
apply combine_bit_low.
assumption.
Qed.

Lemma wlsb_bit : forall n (w : word (S n)),
  Word.wlsb w = get_bit w 0.
intros.
rewrite (Word.shatter_word w).
reflexivity.
Qed.

Lemma get_bit_equiv : forall n (w : word n) i, i < n -> get_bit w i = get_bit_by_shift w i.
destruct w.
* intros.
  reflexivity.
* intros.
  simpl (get_bit_by_shift _ _).
  rewrite wlsb_bit.
  rewrite wrshift_bit; auto.
  Lia.lia.
Qed.

Definition set_bit [n] : word n -> nat -> bool -> word n :=
match n with
| O => fun (w : Word.word O) i b => w
| S n => fun (w : Word.word (S n)) i (b : bool) =>
  let bit : Word.word (S n) := Word.wlshift' (Word.natToWord _ 1) i in
  let mask : Word.word (S n) := Word.wnot bit in
  let masked := Word.wand mask w in
  if b then Word.wor masked bit else masked
end.

Definition word_to_Z [n] (w : word n) : Z := Word.wordToZ w.
Definition word_to_N [n] (w : word n) : N := Word.wordToN w.
Definition Z_to_word n z : word n := Word.ZToWord n z.
Definition N_to_word m n : word m := Word.NToWord m n.

Lemma word_to_N_range : forall [n] (w : word n), (word_to_N w < 2 ^ N.of_nat n)%N.
intros.
change 2%N with (N.of_nat 2).
rewrite <- Nat2N.inj_pow.
rewrite <- NatLib.pow2_N.
apply Word.wordToN_bound.
Qed.

Lemma word_to_Z_range : forall [n] (w : word (S n)), (- 2 ^ Z.of_nat n <= word_to_Z w < 2 ^ Z.of_nat n)%Z.
intros.
change 2%Z with (Z.of_nat 2).
rewrite <- Nat2Z.inj_pow.
apply Word.wordToZ_size'.
Qed.

Local Fixpoint word_to_bools_aux {n} (w:word n) acc :=
match w with
| Word.WO => acc
| Word.WS b w => word_to_bools_aux w (b::acc)%list
end.

Definition word_to_bools [n] (w : word n) : list bool := word_to_bools_aux w [].

Local Lemma word_to_bools_aux_nth : forall n (w : word n) l i,
  List.nth_error (word_to_bools_aux w l) (n + i) = List.nth_error l i.
induction w.
* reflexivity.
* intros.
  simpl (word_to_bools_aux _ _).
  rewrite Nat.add_succ_comm.
  rewrite IHw.
  reflexivity.
Qed.

Lemma word_to_bools_length : forall [n] (w : word n), List.length (word_to_bools w) = n.
intros.
unfold word_to_bools.
rewrite plus_n_O.
change 0 with (List.length ([] : list bool)).
generalize (@nil bool).
induction n.
* dependent inversion w.
  reflexivity.
* intro.
  dependent inversion w; subst.
  simpl.
  rewrite IHn.
  simpl.
  apply Nat.add_succ_r.
Qed.

Lemma word_to_bools_get_bit : forall [n] (w : word n) (i : nat) x,
  List.nth_error (word_to_bools w) i = Some x <-> get_bit w (n - i - 1) = x /\ i < n.
intros.
split.
- intro H.
  specialize (List.nth_error_Some (word_to_bools w) i) as [LEN _].
  rewrite H in LEN.
  specialize (LEN ltac:(congruence)).
  rewrite word_to_bools_length in LEN.
  split; [|assumption].

  unfold word_to_bools in H.
  revert H.
  generalize (@nil bool).
  induction w.
  * Lia.lia.
  * destruct (Nat.eq_dec i n).
    + subst.
      intros.
      assert (x = b). {
        clear -H.
        revert H.
        simpl.
        rewrite (plus_n_O n) at 2.
        rewrite word_to_bools_aux_nth.
        simpl. congruence.
      }
      subst.
      replace (S n - n - 1) with 0 by Lia.lia.
      reflexivity.
    + replace (S n - i - 1) with (S (n - i - 1)) by Lia.lia.
      simpl.
      intros.
      apply IHw with (l := List.cons b l); [Lia.lia|].
      assumption.
- intros [GET LT].
  unfold word_to_bools.
  generalize (@nil bool).
  induction w.
  * Lia.lia.
  * destruct (Nat.eq_dec i n).
    + subst.
      intro.
      rewrite (plus_n_O n) at 3.
      simpl (word_to_bools_aux _ _).
      rewrite word_to_bools_aux_nth.
      replace (S n - n - 1) with 0 by Lia.lia.
      reflexivity.
    + intro.
      simpl (word_to_bools_aux _ _).
      apply IHw; [|Lia.lia].
      replace (S n - i - 1) with (S (n - i - 1)) in GET by Lia.lia.
      apply GET.
Qed.

Fixpoint bools_to_word_rev l : word (length l) :=
match l with
| [] => Word.WO
| b::t => Word.WS b (bools_to_word_rev t)
end%list.
Definition bools_to_word l : word (length l) :=
  cast_nat (bools_to_word_rev (List.rev l)) (List.rev_length l).

Lemma get_bit_cast_word m n (w : word m) (E : m = n) i :
  get_bit (cast_nat w E) i = get_bit w i.
subst.
rewrite cast_nat_refl.
reflexivity.
Qed.

Local Lemma bools_to_word_rev_get_bit : forall l i b,
  List.nth_error l i = Some b <-> get_bit (bools_to_word_rev l) i = b /\ i < length l.
induction l.
* destruct i; intros; split; simpl; intro; solve [congruence|Lia.lia].
* intros.
  destruct i.
  - simpl. intuition; solve [ congruence | Lia.lia ].
  - simpl. rewrite IHl.
    intuition.
Qed.

Lemma nth_error_rev A (l : list A) i x :
  List.nth_error l i = Some x <-> List.nth_error (List.rev l) (length l - i - 1) = Some x /\ i < length l.
destruct (lt_dec i (length l)) as [H|H].
* rewrite List.nth_error_nth' with (d := x); auto.
  rewrite List.nth_error_nth' with (d := x). 2: {
    rewrite List.rev_length.
    Lia.lia.
  }
  rewrite List.rev_nth. 2: Lia.lia.
  replace (length l - S (length l - i - 1)) with i by Lia.lia.
  tauto.
* apply not_lt in H.
  specialize (List.nth_error_None l i) as H'.
  intuition; solve [congruence | Lia.lia].
Qed.

Lemma bools_to_word_get_bit : forall l i b,
  List.nth_error l i = Some b <-> get_bit (bools_to_word l) (length l - i - 1) = b /\ i < length l.
intros.
unfold bools_to_word.
rewrite get_bit_cast_word.
rewrite nth_error_rev.
rewrite bools_to_word_rev_get_bit.
intuition.
rewrite List.rev_length.
Lia.lia.
Qed.

Lemma wrshift_alt : forall sz (w: word sz) n, Word.wrshift' w n = Word.wrshift w n.
intros.
unfold Word.wrshift, Word.wrshift'.
f_equal.
generalize (Word.combine w (Word.wzero n)).
generalize (Nat.add_comm sz n).
generalize (Nat.add_comm n sz).
generalize (sz + n).
intros n' e.
subst.
intros.
rewrite DepEqNat.nat_cast_proof_irrel with (e2 := eq_refl).
rewrite DepEqNat.nat_cast_same.
reflexivity.
Qed.

Lemma wzero_msb : forall sz H, Word.wzero (S sz) = eq_rect _ _ (Word.combine (Word.wzero sz) (Word.wzero 1)) _ H.
induction sz.
* simpl. intros [].
  reflexivity.
* intros H.
  change (Word.wzero (S (S sz))) with (Word.WS false (Word.wzero (S sz))).
  erewrite IHsz at 1.
  erewrite <- Word.WS_eq_rect.
  eapply eq_refl.
  Unshelve.
  Lia.lia.
Qed.

Lemma word_to_N_get_bit : forall [n] (w: word n) i, i < n -> get_bit w i = N.testbit (word_to_N w) (N.of_nat i).
unfold word_to_N.
intros n w i; revert n w.
induction i.
* intros.
  dependent inversion w as [|b n' w']; subst.
  + Lia.lia.
  + simpl.
    destruct b; destruct (Word.wordToN w'); reflexivity.
* intros n w LT.
  dependent inversion w as [|b n' w']; subst.
  + Lia.lia.
  + simpl (get_bit _ _).
    simpl (Word.wordToN _).
    rewrite IHi; [|Lia.lia].
    rewrite Nat2N.inj_succ.
    destruct b.
    - destruct (Word.wordToN w');
      rewrite N.testbit_succ_r_div2; auto; Lia.lia.
    - destruct (Word.wordToN w');
      rewrite N.testbit_succ_r_div2; auto; Lia.lia.
Qed.

Lemma testbit_word_to_N_high : forall [n] (w: word n) i, (i >= N.of_nat n)%N ->
  N.testbit (word_to_N w) i = false.
induction w.
* reflexivity.
* intros i I.
  replace (word_to_N (Word.WS b w)) with (2 * (word_to_N w) + N.b2n b)%N. 2: {
    destruct b; simpl; destruct (word_to_N w); reflexivity.
  }
  destruct (N.zero_or_succ i) as [|[j J]]. Lia.lia.
  subst.
  rewrite N.testbit_succ_r.
  apply IHw.
  Lia.lia.
Qed.
 
Lemma word_to_bools_nth_Some : forall [n] (w : word n) (i : nat) x, n > 0 ->
  List.nth_error (word_to_bools w) i = Some x <-> x = N.testbit (word_to_N w) (N.of_nat (n - i - 1)) /\ i < n.
intros.
rewrite word_to_bools_get_bit.
rewrite word_to_N_get_bit.
intuition.
Lia.lia.
Qed.

Lemma bools_to_word_nth_Some : forall (l : list bool) i b,
  List.nth_error l i = Some b <-> b = N.testbit (word_to_N (bools_to_word l)) (N.of_nat (length l - i - 1)) /\ i < length l.
intros.
destruct l.
* destruct i; simpl; intuition; congruence.
* rewrite bools_to_word_get_bit.
  rewrite word_to_N_get_bit.
  intuition.
  simpl (length _).
  Lia.lia.
Qed.

Local Lemma slice_equality {i n m} : i + n <= m -> m = i + (n + (m - n -i)).
Lia.lia.
Qed.

Definition slice [m] n (w : word m) (i : nat) : word n :=
  match Compare_dec.le_lt_dec (i + n) m with
  | left H =>
      let w : word (i + (n + (m - n - i))) := cast_nat w (slice_equality H) in
      Word.split1 n _ (Word.split2 i _ w)
  | right _ => dummy (zeros _)
  end.

Definition update_slice [m] [n] (w : word m) (i : nat) (v : word n) : word m :=
  match Compare_dec.le_lt_dec (i + n) m with
  | left H =>
    let w : word (i + (n + (m - n - i))) := cast_nat w (slice_equality H) in
    let pre := Word.split1 i _ w in
    let post := Word.split2 n _ (Word.split2 i _ w) in
    let w' := Word.combine pre (Word.combine v post) in
    cast_nat w' (eq_sym (slice_equality H))
  | right _ => dummy (zeros _)
  end.

Definition zero_extend [m] n (w : word m) : word n :=
  match Compare_dec.le_lt_dec m n with
  | left H =>
      cast_nat (Word.zext w (n - m)) (Arith_prebase.le_plus_minus_r_stt _ _ H)
  | right _ => dummy (zeros _)
  end.

Definition sign_extend [m] n (w : word m) : word n :=
  match Compare_dec.le_lt_dec m n with
  | left H =>
      cast_nat (Word.sext w (n - m)) (Arith_prebase.le_plus_minus_r_stt _ _ H)
  | right _ => dummy (zeros _)
  end.

Definition concat [m n] (w: word m) (v: word n) : word (m + n) :=
  cast_nat (Word.combine v w) (Nat.add_comm _ _).

Definition and : forall [n], word n -> word n -> word n := Word.wand.
Definition or  : forall [n], word n -> word n -> word n := Word.wor.
Definition xor : forall [n], word n -> word n -> word n := Word.wxor.
Definition not : forall [n], word n -> word n := Word.wnot.

Definition add : forall [n], word n -> word n -> word n := Word.wplus.
Definition sub : forall [n], word n -> word n -> word n := Word.wminus.
Definition mul : forall [n], word n -> word n -> word n := Word.wmult.

Definition logical_shift_left  [n] (w : word n) i : word n := Word.wlshift' w i.
Definition logical_shift_right [n] (w : word n) i : word n := Word.wrshift' w i.
Definition arith_shift_right   [n] (w : word n) i : word n := Word.wrshifta' w i.

Fixpoint replicate (n : nat) [a] (w : Word.word a) : Word.word (n * a) :=
match n with
| O => Word.WO
| S m => Word.combine w (replicate m w)
end.

Definition eqb [n] (w v : word n) : bool := Word.weqb w v.

Lemma eqb_true_iff [n] (v w : word n) : eqb v w = true <-> v = w.
apply Word.weqb_true_iff.
Qed.

Definition eq_dec [n] (w v : word n) : {w = v} + {w <> v} := Word.weq w v.

Fixpoint reverse_endian [n] (bits : word n) : word n :=
  match n return word n -> word n with
  | S (S (S (S (S (S (S (S m))))))) => fun bits =>
    cast_nat
      (Word.combine
         (reverse_endian (Word.split2 8 m bits))
         (Word.split1 8 m bits))
      (PeanoNat.Nat.add_comm _ _)
  | _ => fun bits => bits
  end bits.

Import String.
Import Strings.Ascii.

Local Fixpoint word_to_binary_string_acc [n] (w : Word.word n) (s : string) :=
  match w with
  | Word.WO => s
  | Word.WS b w' => word_to_binary_string_acc w' (String (if b then "1" else "0")%char s)
  end.
Definition word_to_binary_string [n] (bv : word n) : string := String "0" (String "b" (word_to_binary_string_acc bv "")).


End MachineWord.
