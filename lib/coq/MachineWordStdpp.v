From Sail Require MachineWordInterface.
From stdpp Require base unstable.bitvector.
Require Import ZArith.
Require Import String.

Module MachineWord <: MachineWordInterface.MachineWordInterface.

Definition word n := bitvector.bv (N.of_nat n).

Definition zeros n : word n := bitvector.bv_0 (N.of_nat n).

Definition get_bit [n] (w : word n) i : bool := Z.testbit (bitvector.bv_unsigned w) (Z.of_nat i).

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

Definition word_to_bools [n] (w : word n) : list bool := bitvector.bv_to_bits w.
Definition bools_to_word (l : list bool) : word (List.length l) := N_to_word (List.length l) (Ascii.N_of_digits l).

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
