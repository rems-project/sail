From Sail Require MachineWordInterface.
From stdpp Require base unstable.bitvector.
Require Import ZArith.
Require Import String.

Module MachineWord <: MachineWordInterface.MachineWordInterface.

Definition word n := bitvector.bv (N.of_nat n).

Definition zeros n : word n := bitvector.bv_0 (N.of_nat n).

Definition get_bit [n] (w : word n) i : bool := Z.testbit (bitvector.bv_unsigned w) (Z.of_nat i).

Lemma get_bit_eq : forall [n] (w v : word n),
  (forall i, i < n -> get_bit w i = get_bit v i) -> w = v.
intros n w v H.
apply bitvector.bv_eq.
unfold get_bit in *.
apply Z.bits_inj'.
intros m LE.
destruct (Z_lt_dec m (Z.of_nat n)).
* rewrite <- (Z2Nat.id m LE).
  apply H.
  Lia.lia.
* rewrite !bitvector.bv_unsigned_spec_high; auto; Lia.lia.
Qed.

Definition word_to_Z [n] (w : word n) : Z := bitvector.bv_signed w.
Definition word_to_N [n] (w : word n) : N := Z.to_N (bitvector.bv_unsigned w).
Definition Z_to_word n z : word n := bitvector.Z_to_bv _ z.
Definition N_to_word n nn : word n := bitvector.Z_to_bv _ (Z.of_N nn).

Lemma word_to_N_range : forall [n] (w : word n), (word_to_N w < 2 ^ N.of_nat n)%N.
intros.
specialize (bitvector.bv_unsigned_in_range _ w).
unfold bitvector.bv_modulus.
intros [LE LT].

unfold word_to_N.
rewrite <- (N2Z.id (2 ^ N.of_nat n)).
rewrite <- Z2N.inj_lt;  Lia.lia.
Qed.

(* TODO: this proof is generic, should be shared *)
Lemma testbit_word_to_N_high : forall [n] (w: word n) i, (i >= N.of_nat n)%N ->
  N.testbit (word_to_N w) i = false.
intros.
specialize (word_to_N_range w).
generalize (word_to_N w) as m.
intros.
destruct (N.testbit_spec m i) as [l [h [H1 H2]]].
destruct (N.testbit m i).
* simpl (N.b2n true) in H2. subst.
  assert (l + (1 + 2 * h) * 2 ^ i >= 2 ^ i)%N by Lia.lia.
  specialize (N.pow_le_mono_r 2 (N.of_nat n) i).
  Lia.lia.
* reflexivity.
Qed.

Lemma word_to_Z_range : forall [n] (w : word (S n)), (- 2 ^ Z.of_nat n <= word_to_Z w < 2 ^ Z.of_nat n)%Z.
intros.
specialize (bitvector.bv_signed_in_range _ w ltac:(Lia.lia)).
unfold bitvector.bv_half_modulus, bitvector.bv_modulus, word_to_Z.
rewrite nat_N_Z.
rewrite Nat2Z.inj_succ.
rewrite Z.pow_succ_r; auto with zarith.

replace (2 * 2 ^ Z.of_nat n / 2)%Z with (2 ^ Z.of_nat n)%Z. 2: {
  rewrite Z.mul_comm.
  rewrite Z.div_mul; auto.
}
trivial.
Qed.

Definition ones n : word n := bitvector.Z_to_bv _ (-1).

Definition word_to_bools [n] (w : word n) : list bool := List.rev (bitvector.bv_to_bits w).
Definition bools_to_word (l : list bool) : word (List.length l) := N_to_word (List.length l) (Ascii.N_of_digits (List.rev l)).

Lemma word_to_bools_length : forall [n] (w : word n), List.length (word_to_bools w) = n.
intros.
unfold word_to_bools.
rewrite List.rev_length.
rewrite bitvector.bv_to_bits_length.
apply Nnat.Nat2N.id.
Qed.

Lemma nth_error_lookup {A} (l : list A) (i : nat) :
  base.lookup i l = List.nth_error l i.
destruct (List.nth_error l i) eqn:H.
* specialize (List.nth_error_Some l i) as LEN.
  rewrite H in LEN.
  destruct (list.nth_lookup_or_length l i a).
  - rewrite (List.nth_error_nth l i a H) in e.
    assumption.
  - intuition.
* apply list.lookup_ge_None.
  apply List.nth_error_None.
  assumption.
Qed.

Lemma nth_error_rev A (l : list A) i x :
  List.nth_error l i = Some x <-> List.nth_error (List.rev l) (List.length l - i - 1) = Some x /\ i < List.length l.
destruct (lt_dec i (List.length l)) as [H|H].
* rewrite List.nth_error_nth' with (d := x); auto.
  rewrite List.nth_error_nth' with (d := x). 2: {
    rewrite List.rev_length.
    Lia.lia.
  }
  rewrite List.rev_nth. 2: Lia.lia.
  replace (List.length l - S (List.length l - i - 1)) with i by Lia.lia.
  tauto.
* apply not_lt in H.
  specialize (List.nth_error_None l i) as H'.
  intuition; solve [congruence | Lia.lia].
Qed.

Lemma word_to_bools_get_bit : forall [n] (w : word n) (i : nat) x,
  List.nth_error (word_to_bools w) i = Some x <-> get_bit w (n - i - 1) = x /\ i < n.
intros.
unfold word_to_bools, get_bit.
specialize (bitvector.bv_to_bits_lookup_Some w (n - i - 1) x).
rewrite nth_error_lookup.
intro H.
rewrite nth_error_rev.
rewrite List.rev_involutive, List.rev_length.
rewrite bitvector.bv_to_bits_length.
rewrite Nnat.Nat2N.id.
intuition.
Qed.

Lemma word_to_bools_nth_Some : forall [n] (w : word n) (i : nat) x, n > 0 ->
  List.nth_error (word_to_bools w) i = Some x <-> x = N.testbit (word_to_N w) (N.of_nat (n - i - 1)) /\ i < n.
intros.
rewrite word_to_bools_get_bit.
unfold get_bit, word_to_N.
rewrite <- (Z2N.id (bitvector.bv_unsigned w)) at 1.
rewrite <- nat_N_Z.
rewrite Z.testbit_of_N.
intuition.
firstorder using bitvector.bv_unsigned_in_range.
Qed.

Lemma N_of_digits_limit l :
  (Ascii.N_of_digits l < 2 ^ N.of_nat (List.length l))%N.
induction l.
* simpl. Lia.lia.
* simpl (List.length _).
  rewrite Nnat.Nat2N.inj_succ.
  rewrite N.pow_succ_r'.
  simpl (Ascii.N_of_digits _).
  destruct (Ascii.N_of_digits l); destruct a; Lia.lia.
Qed.

Local Lemma nth_error_N_of_digits l i b :
  List.nth_error l i = Some b <-> N.testbit (Ascii.N_of_digits l) (N.of_nat i) = b /\ i < List.length l.
revert i.
induction l.
* destruct i; simpl; intuition.
* destruct i.
  - destruct a; simpl; destruct (Ascii.N_of_digits l); simpl; intuition.
  - rewrite Nnat.Nat2N.inj_succ.
    replace (Ascii.N_of_digits (a::l)) with (2 * Ascii.N_of_digits l + N.b2n a)%N. 2: {
      simpl Ascii.N_of_digits at 2.
      destruct (Ascii.N_of_digits l).
      + destruct a; simpl; Lia.lia.
      + destruct a; simpl; Lia.lia.
    }
    rewrite N.testbit_succ_r.
    specialize (IHl i).
    intuition.
    simpl; Lia.lia.
Qed.

Lemma bools_to_word_get_bit : forall l i b,
  List.nth_error l i = Some b <-> get_bit (bools_to_word l) (List.length l - i - 1) = b /\ i < List.length l.
intros.
unfold bools_to_word, get_bit, N_to_word.
rewrite bitvector.Z_to_bv_unsigned.
rewrite bitvector.bv_wrap_small. 2: {
  split; [Lia.lia|].
  unfold bitvector.bv_modulus.
  specialize (N_of_digits_limit (List.rev l)).
  rewrite List.rev_length.
  Lia.lia.
}
erewrite <- nat_N_Z.
rewrite Z.testbit_of_N.
rewrite nth_error_rev.
specialize (nth_error_N_of_digits (List.rev l) (List.length l - i - 1) b).
rewrite List.rev_length.
intuition.
Qed.

Lemma bools_to_word_nth_Some : forall (l : list bool) i b,
  List.nth_error l i = Some b <-> b = N.testbit (word_to_N (bools_to_word l)) (N.of_nat (List.length l - i - 1)) /\ i < List.length l.
intros.
rewrite bools_to_word_get_bit.
unfold get_bit, word_to_N.
rewrite <- (Z2N.id (bitvector.bv_unsigned (bools_to_word l))) at 1. 2: {
  specialize (bitvector.bv_unsigned_in_range _ (bools_to_word l)).
  intuition.
}
rewrite <- nat_N_Z.
rewrite Z.testbit_of_N.
intuition.
Qed.

Definition slice {m} n (w : word m) i : word n := bitvector.bv_extract (N.of_nat i) _ w.
Definition update_slice {m n} (w : word m) i (v : word n) : word m :=
  bitvector.bv_concat (N.of_nat m)
    (slice (m - n - i) w (i + n))
    (bitvector.bv_concat (N.of_nat (i+n)) v (slice i w 0)).
Definition zero_extend {m} n (w : word m) : word n := bitvector.bv_zero_extend _ w.
Definition sign_extend {m} n (w : word m) : word n := bitvector.bv_sign_extend _ w.
Definition concat {m n} (w : word m) (v : word n) : word (m + n) := bitvector.bv_concat _ w v.

Definition set_bit [n] (w : word n) i b : word n := update_slice w i (bitvector.bool_to_bv (N.of_nat 1) b).

Definition and [n] (w v : word n) : word n := bitvector.bv_and w v.
Definition  or [n] (w v : word n) : word n := bitvector.bv_or w v.
Definition xor [n] (w v : word n) : word n := bitvector.bv_xor w v.
Definition not [n] (w : word n) : word n := bitvector.bv_not w.

Definition add [n] (w v : word n) : word n := bitvector.bv_add w v.
Definition sub [n] (w v : word n) : word n := bitvector.bv_sub w v.
Definition mul [n] (w v : word n) : word n := bitvector.bv_mul w v.

Definition logical_shift_left  [n] (w : word n) i : word n := bitvector.bv_shiftl w (N_to_word n (N.of_nat i)).
Definition logical_shift_right [n] (w : word n) i : word n := bitvector.bv_shiftr w (N_to_word n (N.of_nat i)).
Definition arith_shift_right   [n] (w : word n) i : word n := bitvector.bv_ashiftr w (N_to_word n (N.of_nat i)).

Fixpoint replicate m [n] (w : word n) : word (m * n) :=
  match m with
  | O => bitvector.bv_0 0
  | S m' => bitvector.bv_concat _ w (replicate m' w)
  end.

Definition eq_dec [n] (w v : word n) : {w = v} + {w <> v} := base.decide (w = v).

Definition eqb [n] (w v : word n) := if eq_dec w v then true else false.
Lemma eqb_true_iff {n} (w v : word n) : eqb w v = true <-> w = v.
unfold eqb.
destruct (eq_dec w v); intuition.
Qed.

Definition reverse_endian [n] (w : word n) : word n :=
  let bytes := bitvector.bv_to_little_endian (Z.div (Z.of_nat n) 8) 8 (bitvector.bv_unsigned w) in
  Z_to_word n (bitvector.little_endian_to_bv 8 (List.rev bytes)).

Definition word_to_binary_string [n] (w : word n) : String.string :=
  let bits := word_to_bools w in
  let digits := List.map (fun b : bool => if b then "1" else "0")%string bits in
  String.concat "" digits.

End MachineWord.
