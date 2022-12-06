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

Definition cast_word {m n} (x : Word.word m) (eq : m = n) : Word.word n :=
  DepEqNat.nat_cast _ eq x.

Definition word := Word.word.
Definition zeros n := @Word.wzero n.
Definition ones n := @Word.wones n.
Definition get_bit {n} :=
  match n with
  | O => fun (w : Word.word O) i => dummy false
  | S n => fun (w : Word.word (S n)) i => Word.wlsb (Word.wrshift' w i)
  end.

Definition set_bit {n} :=
match n with
| O => fun (w : Word.word O) i b => w
| S n => fun (w : Word.word (S n)) i (b : bool) =>
  let bit : Word.word (S n) := Word.wlshift' (Word.natToWord _ 1) i in
  let mask : Word.word (S n) := Word.wnot bit in
  let masked := Word.wand mask w in
  if b then Word.wor masked bit else masked
end.

Definition word_to_Z {n} (w : word n) := Word.wordToZ w.
Definition word_to_N {n} (w : word n) := Word.wordToN w.
Definition Z_to_word n z := Word.ZToWord n z.
Definition N_to_word m n := Word.NToWord m n.

Lemma word_to_N_range : forall {n} (w : word n), (word_to_N w < 2 ^ N.of_nat n)%N.
intros.
change 2%N with (N.of_nat 2).
rewrite <- Nat2N.inj_pow.
rewrite <- NatLib.pow2_N.
apply Word.wordToN_bound.
Qed.

Lemma word_to_Z_range : forall {n} (w : word (S n)), (- 2 ^ Z.of_nat n <= word_to_Z w < 2 ^ Z.of_nat n)%Z.
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

Definition word_to_bools {n} (w : word n) := word_to_bools_aux w [].

Fixpoint bools_to_word_rev l : word (length l) :=
match l with
| [] => Word.WO
| b::t => Word.WS b (bools_to_word_rev t)
end%list.
Definition bools_to_word l : word (length l) :=
  cast_word (bools_to_word_rev (List.rev l)) (List.rev_length l).

Local Lemma slice_equality {i n m} : i + n <= m -> m = i + (n + (m - n -i)).
Lia.lia.
Qed.

Definition slice {m} n (w : word m) (i : nat) : word n :=
  match Compare_dec.le_lt_dec (i + n) m with
  | left H =>
      let w : word (i + (n + (m - n - i))) := cast_word w (slice_equality H) in
      Word.split1 n _ (Word.split2 i _ w)
  | right _ => dummy (zeros _)
  end.

Definition update_slice {m} {n} (w : word m) (i : nat) (v : word n) : word m :=
  match Compare_dec.le_lt_dec (i + n) m with
  | left H =>
    let w : word (i + (n + (m - n - i))) := cast_word w (slice_equality H) in
    let pre := Word.split1 i _ w in
    let post := Word.split2 n _ (Word.split2 i _ w) in
    let w' := Word.combine pre (Word.combine v post) in
    eq_rect _ _ w' _ (eq_sym (slice_equality H))
  | right _ => dummy (zeros _)
  end.

Definition zero_extend {m} n (w : word m) : word n :=
  match Compare_dec.le_lt_dec m n with
  | left H =>
      cast_word (Word.zext w (n - m)) (Arith_prebase.le_plus_minus_r_stt _ _ H)
  | right _ => dummy (zeros _)
  end.

Definition sign_extend {m} n (w : word m) : word n :=
  match Compare_dec.le_lt_dec m n with
  | left H =>
      cast_word (Word.sext w (n - m)) (Arith_prebase.le_plus_minus_r_stt _ _ H)
  | right _ => dummy (zeros _)
  end.

Definition concat {m n} (w: word m) (v: word n) := Word.combine w v.

Definition and := Word.wand.
Definition or := Word.wor.
Definition xor := Word.wxor.
Definition not := Word.wnot.

Definition add := Word.wplus.
Definition sub := Word.wminus.
Definition mul := Word.wmult.

Definition logical_shift_left {n} (w : word n) i := Word.wlshift' w i.
Definition logical_shift_right {n} (w : word n) i := Word.wrshift' w i.
Definition arith_shift_right {n} (w : word n) i := Word.wrshifta' w i.

Fixpoint replicate (n : nat) {a} (w : Word.word a) : Word.word (n * a) :=
match n with
| O => Word.WO
| S m => Word.combine w (replicate m w)
end.

Definition eqb {n} (w v : word n) := Word.weqb w v.

Lemma eqb_true_iff {n} (v w : word n) : eqb v w = true <-> v = w.
apply Word.weqb_true_iff.
Qed.

Definition eq_dec {n} (w v : word n) := Word.weq w v.

Fixpoint reverse_endian {n} (bits : word n) : word n :=
  match n return word n -> word n with
  | S (S (S (S (S (S (S (S m))))))) => fun bits =>
    cast_word
      (Word.combine
         (reverse_endian (Word.split2 8 m bits))
         (Word.split1 8 m bits))
      (PeanoNat.Nat.add_comm _ _)
  | _ => fun bits => bits
  end bits.

Import String.
Import Strings.Ascii.

Local Fixpoint word_to_binary_string_acc {n} (w : Word.word n) (s : string) :=
  match w with
  | Word.WO => s
  | Word.WS b w' => word_to_binary_string_acc w' (String (if b then "1" else "0")%char s)
  end.
Definition word_to_binary_string {n} (bv : word n) := String "0" (String "b" (word_to_binary_string_acc bv "")).


End MachineWord.
