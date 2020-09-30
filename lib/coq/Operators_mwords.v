Require Import Sail.Values.
Require Import Sail.Operators.
Require Import Sail.Prompt_monad.
Require Import Sail.Prompt.
Require Import bbv.Word.
Require bbv.BinNotation.
Require Import Arith.
Require Import ZArith.
Require Import Lia.
Require Import Eqdep_dec.
Local Open Scope Z.

Fixpoint cast_positive (T : positive -> Type) (p q : positive) : T p -> p = q -> T q.
refine (
match p, q with
| xH, xH => fun x _ => x
| xO p', xO q' => fun x e => cast_positive (fun x => T (xO x)) p' q' x _
| xI p', xI q' => fun x e => cast_positive (fun x => T (xI x)) p' q' x _
| _, _ => _
end); congruence.
Defined.

Definition cast_T {T : Z -> Type} {m n} : forall (x : T m) (eq : m = n), T n.
refine (match m,n with
| Z0, Z0 => fun x _ => x
| Zneg p1, Zneg p2 => fun x e => cast_positive (fun p => T (Zneg p)) p1 p2 x _
| Zpos p1, Zpos p2 => fun x e => cast_positive (fun p => T (Zpos p)) p1 p2 x _
| _,_ => _
end); congruence.
Defined.

Lemma cast_positive_refl : forall p T x (e : p = p),
  cast_positive T p p x e = x.
induction p.
* intros. simpl. rewrite IHp; auto.
* intros. simpl. rewrite IHp; auto.
* reflexivity.
Qed.

Lemma cast_T_refl {T : Z -> Type} {m} {H:m = m} (x : T m) : cast_T x H = x.
destruct m.
* reflexivity.
* simpl. rewrite cast_positive_refl. reflexivity.
* simpl. rewrite cast_positive_refl. reflexivity.
Qed.

Definition autocast {T : Z -> Type} {m n} (x : T m) `{H:ArithFact (m =? n)} : T n.
refine (cast_T x _).
apply Z.eqb_eq.
apply (use_ArithFact H).
Defined.

Definition autocast_m {rv e m n} (x : monad rv (mword m) e) `{H:ArithFact (m =? n)} : monad rv (mword n) e.
refine (x >>= fun x => returnm (cast_T x _)).
apply Z.eqb_eq.
apply (use_ArithFact H).
Defined.

Definition cast_word {m n} (x : Word.word m) (eq : m = n) : Word.word n :=
  DepEqNat.nat_cast _ eq x.

Lemma cast_word_refl {m} {H:m = m} (x : word m) : cast_word x H = x.
rewrite (UIP_refl_nat _ H).
apply nat_cast_same.
Qed.

Definition mword_of_nat {m} : Word.word m -> mword (Z.of_nat m).
refine (match m return word m -> mword (Z.of_nat m) with
| O => fun x => x
| S m' => fun x => nat_cast _ _ x
end).
rewrite SuccNat2Pos.id_succ.
reflexivity.
Defined.

Definition cast_to_mword {m n} (x : Word.word m) : Z.of_nat m = n -> mword n.
refine (match n return Z.of_nat m = n -> mword n with
| Z0 => fun _ => WO
| Zpos p => fun eq => cast_T (mword_of_nat x) eq
| Zneg p => _
end).
intro eq.
exfalso. destruct m; simpl in *; congruence.
Defined.

(*
(* Specialisation of operators to machine words *)

val access_vec_inc : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
Definition access_vec_inc {a} : mword a -> Z -> bitU := access_mword_inc.

(*val access_vec_dec : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
Definition access_vec_dec {a} : mword a -> Z -> bitU := access_mword_dec.

(*val update_vec_inc : forall 'a. Size 'a => mword 'a -> integer -> bitU -> mword 'a*)
(* TODO: probably ought to use a monadic version instead, but using bad default for
   type compatibility just now *)
Definition update_vec_inc {a} (w : mword a) i b : mword a :=
 opt_def w (update_mword_inc w i b).

(*val update_vec_dec : forall 'a. Size 'a => mword 'a -> integer -> bitU -> mword 'a*)
Definition update_vec_dec {a} (w : mword a) i b : mword a := opt_def w (update_mword_dec w i b).

Lemma subrange_lemma0 {n m o} `{ArithFact (0 <=? o)} `{ArithFact (o <=? m <? n)} : (Z.to_nat o <= Z.to_nat m < Z.to_nat n)%nat.
intros.
unwrap_ArithFacts.
unbool_comparisons.
split.
+ apply Z2Nat.inj_le; lia.
+ apply Z2Nat.inj_lt; lia.
Qed.
Lemma subrange_lemma1 {n m o} : (o <= m < n -> n = m + 1 + (n - (m + 1)))%nat.
intros. lia.
Qed.
Lemma subrange_lemma2 {n m o} : (o <= m < n -> m+1 = o+(m-o+1))%nat.
lia.
Qed.
Lemma subrange_lemma3 {m o} `{ArithFact (0 <=? o)} `{ArithFact (o <=? m)} :
  Z.of_nat (Z.to_nat m - Z.to_nat o + 1)%nat = m - o + 1.
unwrap_ArithFacts.
unbool_comparisons.
rewrite Nat2Z.inj_add.
rewrite Nat2Z.inj_sub.
repeat rewrite Z2Nat.id; lia.
apply Z2Nat.inj_le; lia.
Qed.

Definition subrange_vec_dec {n} (v : mword n) m o `{ArithFact (0 <=? o)} `{ArithFact (o <=? m <? n)} : mword (m - o + 1) :=
  let n := Z.to_nat n in
  let m := Z.to_nat m in
  let o := Z.to_nat o in
  let prf : (o <= m < n)%nat := subrange_lemma0 in
  let w := get_word v in
  cast_to_mword (split2 o (m-o+1)
                        (cast_word (split1 (m+1) (n-(m+1)) (cast_word w (subrange_lemma1 prf)))
                                   (subrange_lemma2 prf))) subrange_lemma3.

Definition subrange_vec_inc {n} (v : mword n) m o `{ArithFact (0 <=? m)} `{ArithFact (m <=? o <? n)} : mword (o - m + 1) := autocast (subrange_vec_dec v (n-1-m) (n-1-o)).

(* TODO: get rid of bogus default *)
Parameter dummy_vector : forall {n} `{ArithFact (n >=? 0)}, mword n.

(*val update_subrange_vec_inc : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
Definition update_subrange_vec_inc_unchecked {a b} (v : mword a) i j (w : mword b) : mword a :=
  opt_def dummy_vector (of_bits (update_subrange_bv_inc v i j w)).

(*val update_subrange_vec_dec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
Definition update_subrange_vec_dec_unchecked {a b} (v : mword a) i j (w : mword b) : mword a :=
  opt_def dummy_vector (of_bits (update_subrange_bv_dec v i j w)).

Lemma update_subrange_vec_dec_pf {o m n} :
ArithFact (0 <=? o) ->
ArithFact (o <=? m <? n) ->
Z.of_nat (Z.to_nat o + (Z.to_nat (m - o + 1) + (Z.to_nat n - (Z.to_nat m + 1)))) = n.
intros [H1] [H2].
unbool_comparisons.
rewrite <- subrange_lemma3.
rewrite !Nat2Z.inj_add.
rewrite !Nat2Z.inj_sub.
rewrite Nat2Z.inj_add.
repeat rewrite Z2Nat.id; lia.
rewrite Nat.add_1_r.
apply Z2Nat.inj_lt; lia.
apply Z2Nat.inj_le; lia.
Qed.

Definition update_subrange_vec_dec {n} (v : mword n) m o `{ArithFact (0 <=? o)} `{ArithFact (o <=? m <? n)} (w : mword (m - o + 1)) : mword n.
refine (
  let n := Z.to_nat n in
  let m := Z.to_nat m in
  let o := Z.to_nat o in
  let prf : (o <= m < n)%nat := subrange_lemma0 in
  let v' := get_word v in
  let w' := get_word w in
  let x :=
    split1 o (m-o+1)
      (cast_word (split1 (m+1) (n-(m+1)) (cast_word v' (subrange_lemma1 prf)))
        (subrange_lemma2 prf)) in
  let y :=
      split2 (m+1) (n-(m+1)) (cast_word v' (subrange_lemma1 prf)) in
  let z := combine x (combine w' y) in
  cast_to_mword z (update_subrange_vec_dec_pf _ _)).
Defined.

Definition update_subrange_vec_inc {n} (v : mword n) m o `{ArithFact (0 <=? m)} `{ArithFact (m <=? o <? n)} (w : mword (o - m + 1)) : mword n := update_subrange_vec_dec v (n-1-m) (n-1-o) (autocast w).

Lemma mword_nonneg {a} : mword a -> a >= 0.
destruct a.
1,2: auto using Z.le_ge, Zle_0_pos with zarith.
destruct 1.
Qed.

(*val extz_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition extz_vec {a b} `{ArithFact (b >=? a)} (n : Z) (v : mword a) : mword b.
refine (cast_to_mword (Word.zext (get_word v) (Z.to_nat (b - a))) _).
unwrap_ArithFacts.
unbool_comparisons.
assert (a >= 0). { apply mword_nonneg. assumption. }
rewrite <- Z2Nat.inj_add; [ | lia | lia ].
rewrite Zplus_minus.
apply Z2Nat.id.
auto with zarith.
Defined.

(*val exts_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition exts_vec {a b} `{ArithFact (b >=? a)} (n : Z) (v : mword a) : mword b.
refine (cast_to_mword (Word.sext (get_word v) (Z.to_nat (b - a))) _).
unwrap_ArithFacts.
unbool_comparisons.
assert (a >= 0). { apply mword_nonneg. assumption. }
rewrite <- Z2Nat.inj_add; [ | lia | lia ].
rewrite Zplus_minus.
apply Z2Nat.id.
auto with zarith.
Defined.

Definition zero_extend {a} (v : mword a) (n : Z) `{ArithFact (n >=? a)} : mword n := extz_vec n v.

Definition sign_extend {a} (v : mword a) (n : Z) `{ArithFact (n >=? a)} : mword n := exts_vec n v.

Definition zeros (n : Z) `{ArithFact (n >=? 0)} : mword n.
refine (cast_to_mword (Word.wzero (Z.to_nat n)) _).
unwrap_ArithFacts.
unbool_comparisons.
apply Z2Nat.id.
auto with zarith.
Defined.

Lemma truncate_eq {m n} : m >= 0 -> m <= n -> (Z.to_nat n = Z.to_nat m + (Z.to_nat n - Z.to_nat m))%nat.
intros.
assert ((Z.to_nat m <= Z.to_nat n)%nat).
{ apply Z2Nat.inj_le; lia. }
lia.
Qed.
Lemma truncateLSB_eq {m n} : m >= 0 -> m <= n -> (Z.to_nat n = (Z.to_nat n - Z.to_nat m) + Z.to_nat m)%nat.
intros.
assert ((Z.to_nat m <= Z.to_nat n)%nat).
{ apply Z2Nat.inj_le; lia. }
lia.
Qed.

Definition vector_truncate {n} (v : mword n) (m : Z) `{ArithFact (m >=? 0)} `{ArithFact (m <=? n)} : mword m.
refine (cast_to_mword (Word.split1 _ _ (cast_word (get_word v) (_ : Z.to_nat n = Z.to_nat m + (Z.to_nat n - Z.to_nat m))%nat)) (_ : Z.of_nat (Z.to_nat m) = m)).
abstract (unwrap_ArithFacts; unbool_comparisons; apply truncate_eq; auto with zarith).
abstract (unwrap_ArithFacts; unbool_comparisons; apply Z2Nat.id; lia).
Defined.

Definition vector_truncateLSB {n} (v : mword n) (m : Z) `{ArithFact (m >=? 0)} `{ArithFact (m <=? n)} : mword m.
refine (cast_to_mword (Word.split2 _ _ (cast_word (get_word v) (_ : Z.to_nat n = (Z.to_nat n - Z.to_nat m) + Z.to_nat m)%nat)) (_ : Z.of_nat (Z.to_nat m) = m)).
abstract (unwrap_ArithFacts; unbool_comparisons; apply truncateLSB_eq; auto with zarith).
abstract (unwrap_ArithFacts; unbool_comparisons; apply Z2Nat.id; lia).
Defined.

Lemma concat_eq {a b} : a >= 0 -> b >= 0 -> Z.of_nat (Z.to_nat b + Z.to_nat a)%nat = a + b.
intros.
rewrite Nat2Z.inj_add.
rewrite Z2Nat.id. 2: solve [ auto with zarith ].
rewrite Z2Nat.id; auto with zarith.
Qed.


(*val concat_vec : forall 'a 'b 'c. Size 'a, Size 'b, Size 'c => mword 'a -> mword 'b -> mword 'c*)
Definition concat_vec {a b} (v : mword a) (w : mword b) : mword (a + b) :=
 cast_to_mword (Word.combine (get_word w) (get_word v)) (ltac:(solve [auto using concat_eq, mword_nonneg with zarith]) : Z.of_nat (Z.to_nat b + Z.to_nat a)%nat = a + b).

(*val cons_vec : forall 'a 'b 'c. Size 'a, Size 'b => bitU -> mword 'a -> mword 'b*)
(*Definition cons_vec {a b} : bitU -> mword a -> mword b := cons_bv.*)

(*val bool_of_vec : mword ty1 -> bitU
Definition bool_of_vec := bool_of_bv

val cast_unit_vec : bitU -> mword ty1
Definition cast_unit_vec := cast_unit_bv

val vec_of_bit : forall 'a. Size 'a => integer -> bitU -> mword 'a
Definition vec_of_bit := bv_of_bit*)

Require Import bbv.NatLib.

Lemma Npow2_pow {n} : (2 ^ (N.of_nat n) = Npow2 n)%N.
induction n.
* reflexivity.
* rewrite Nnat.Nat2N.inj_succ.
  rewrite N.pow_succ_r'.
  rewrite IHn.
  rewrite Npow2_S.
  rewrite Word.Nmul_two.
  reflexivity.
Qed.

Definition uint_plain {a} (x : mword a) : Z :=
  Z.of_N (Word.wordToN (get_word x)).

Program Definition uint {a} (x : mword a) : {z : Z & ArithFact (0 <=? z <=? 2 ^ a - 1)} :=
 existT _ (uint_plain x) _.
Next Obligation.
constructor.
apply Bool.andb_true_iff.
constructor.
* apply Z.leb_le. apply N2Z.is_nonneg.
* apply Z.leb_le.
  assert (2 ^ a - 1 = Z.of_N (2 ^ (Z.to_N a) - 1)). {
    rewrite N2Z.inj_sub.
    * rewrite N2Z.inj_pow.
      rewrite Z2N.id. solve [ auto ].
      destruct a. 1,2: auto with zarith. destruct x.
    * apply N.le_trans with (m := (2^0)%N). solve [ auto using N.le_refl ].
      apply N.pow_le_mono_r.
      inversion 1.
      apply N.le_0_l.
  }
  rewrite H.
  apply N2Z.inj_le.
  rewrite N.sub_1_r.
  apply N.lt_le_pred.
  rewrite <- Z_nat_N.
  rewrite Npow2_pow.
  apply Word.wordToN_bound.
Defined.

Lemma Zpow_pow2 {n} : 2 ^ Z.of_nat n = Z.of_nat (pow2 n).
induction n.
* reflexivity.
* rewrite pow2_S_z.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r; auto with zarith.
Qed.

Definition sint_plain {a} (x : mword a) : Z :=
  Word.wordToZ (get_word x).

Program Definition sint {a} `{ArithFact (a >? 0)} (x : mword a) : {z : Z & ArithFact (-(2^(a-1)) <=? z <=? 2 ^ (a-1) - 1)} :=
  existT _ (sint_plain x) _.
Next Obligation.
unfold sint_plain.
destruct H.
unbool_comparisons.
destruct a; try inversion fact.
constructor.
unbool_comparisons_goal.
generalize (get_word x).
rewrite <- positive_nat_Z.
destruct (Pos2Nat.is_succ p) as [n eq].
rewrite eq.
rewrite Nat2Z.id.
intro w.
destruct (Word.wordToZ_size' w) as [LO HI].
replace 1 with (Z.of_nat 1). 2: solve [ auto ].
rewrite <- Nat2Z.inj_sub. 2: solve [ auto with arith ].
simpl.
rewrite <- minus_n_O.
rewrite Zpow_pow2.
rewrite Z.sub_1_r.
rewrite <- Z.lt_le_pred.
auto.
Defined.

Definition sint0 {a} `{ArithFact (a >=? 0)} (x : mword a) : Z :=
  if sumbool_of_bool (Z.eqb a 0) then 0 else projT1 (sint x).

Lemma length_list_pos : forall {A} {l:list A}, 0 <= Z.of_nat (List.length l).
unfold length_list.
auto with zarith.
Qed.
Hint Resolve length_list_pos : sail.

Definition vec_of_bits (l:list bitU) : mword (length_list l) := opt_def dummy_vector (of_bits l).
(*

val msb : forall 'a. Size 'a => mword 'a -> bitU
Definition msb := most_significant

val int_of_vec : forall 'a. Size 'a => bool -> mword 'a -> integer
Definition int_of_vec := int_of_bv

val string_of_vec : forall 'a. Size 'a => mword 'a -> string*)
Definition string_of_bits {n} (w : mword n) : string := string_of_bv w.
Definition with_word' {n} (P : Type -> Type) : (forall n, Word.word n -> P (Word.word n)) -> mword n -> P (mword n) := fun f w => @with_word n _ (f (Z.to_nat n)) w.
Definition word_binop {n} (f : forall n, Word.word n -> Word.word n -> Word.word n) : mword n -> mword n -> mword n := with_word' (fun x => x -> x) f.
Definition word_unop {n} (f : forall n, Word.word n -> Word.word n) : mword n -> mword n := with_word' (fun x => x) f.


(*
val and_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val or_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val xor_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val not_vec : forall 'a. Size 'a => mword 'a -> mword 'a*)
Definition and_vec {n} : mword n -> mword n -> mword n := word_binop Word.wand.
Definition or_vec  {n} : mword n -> mword n -> mword n := word_binop Word.wor.
Definition xor_vec {n} : mword n -> mword n -> mword n := word_binop Word.wxor.
Definition not_vec {n} : mword n -> mword n := word_unop Word.wnot.

(*val add_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val sadd_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val sub_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val mult_vec  : forall 'a 'b. Size 'a, Size 'b => mword 'a -> mword 'a -> mword 'b
val smult_vec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> mword 'a -> mword 'b*)
Definition add_vec   {n} : mword n -> mword n -> mword n := word_binop Word.wplus.
(*Definition sadd_vec  {n} : mword n -> mword n -> mword n := sadd_bv w.*)
Definition sub_vec   {n} : mword n -> mword n -> mword n := word_binop Word.wminus.
Definition mult_vec  {n m} `{ArithFact (m >=? n)} (l : mword n) (r : mword n) : mword m :=
  word_binop Word.wmult (zero_extend l _) (zero_extend r _).
Definition mults_vec  {n m} `{ArithFact (m >=? n)} (l : mword n) (r : mword n) : mword m :=
  word_binop Word.wmult (sign_extend l _) (sign_extend r _).

(*val add_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val sadd_vec_int  : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val sub_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val mult_vec_int  : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b
val smult_vec_int : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
Definition add_vec_int   {a} (l : mword a) (r : Z) : mword a := arith_op_bv_int Z.add   false l r.
Definition sadd_vec_int  {a} (l : mword a) (r : Z) : mword a := arith_op_bv_int Z.add   true  l r.
Definition sub_vec_int   {a} (l : mword a) (r : Z) : mword a := arith_op_bv_int Z.sub   false l r.
(*Definition mult_vec_int  {a b} : mword a -> Z -> mword b := mult_bv_int.
Definition smult_vec_int {a b} : mword a -> Z -> mword b := smult_bv_int.*)

(*val add_int_vec   : forall 'a. Size 'a => integer -> mword 'a -> mword 'a
val sadd_int_vec  : forall 'a. Size 'a => integer -> mword 'a -> mword 'a
val sub_int_vec   : forall 'a. Size 'a => integer -> mword 'a -> mword 'a
val mult_int_vec  : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b
val smult_int_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b
Definition add_int_vec   := add_int_bv
Definition sadd_int_vec  := sadd_int_bv
Definition sub_int_vec   := sub_int_bv
Definition mult_int_vec  := mult_int_bv
Definition smult_int_vec := smult_int_bv

val add_vec_bit  : forall 'a. Size 'a => mword 'a -> bitU -> mword 'a
val sadd_vec_bit : forall 'a. Size 'a => mword 'a -> bitU -> mword 'a
val sub_vec_bit  : forall 'a. Size 'a => mword 'a -> bitU -> mword 'a
Definition add_vec_bit  := add_bv_bit
Definition sadd_vec_bit := sadd_bv_bit
Definition sub_vec_bit  := sub_bv_bit

val add_overflow_vec         : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
val add_overflow_vec_signed  : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
val sub_overflow_vec         : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
val sub_overflow_vec_signed  : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
val mult_overflow_vec        : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
val mult_overflow_vec_signed : forall 'a. Size 'a => mword 'a -> mword 'a -> (mword 'a * bitU * bitU)
Definition add_overflow_vec         := add_overflow_bv
Definition add_overflow_vec_signed  := add_overflow_bv_signed
Definition sub_overflow_vec         := sub_overflow_bv
Definition sub_overflow_vec_signed  := sub_overflow_bv_signed
Definition mult_overflow_vec        := mult_overflow_bv
Definition mult_overflow_vec_signed := mult_overflow_bv_signed

val add_overflow_vec_bit         : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val add_overflow_vec_bit_signed  : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val sub_overflow_vec_bit         : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val sub_overflow_vec_bit_signed  : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
Definition add_overflow_vec_bit         := add_overflow_bv_bit
Definition add_overflow_vec_bit_signed  := add_overflow_bv_bit_signed
Definition sub_overflow_vec_bit         := sub_overflow_bv_bit
Definition sub_overflow_vec_bit_signed  := sub_overflow_bv_bit_signed

val shiftl       : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val shiftr       : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val arith_shiftr : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val rotl         : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val rotr         : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(* TODO: check/redefine behaviour on out-of-range n *)
Definition shiftl       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wlshift' w (Z.to_nat n)) v.
Definition shiftr       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wrshift' w (Z.to_nat n)) v.
Definition arith_shiftr {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wrshifta' w (Z.to_nat n)) v.
(*
Definition rotl         := rotl_bv
Definition rotr         := rotr_bv

val mod_vec         : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val quot_vec        : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
val quot_vec_signed : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a
Definition mod_vec         := mod_bv
Definition quot_vec        := quot_bv
Definition quot_vec_signed := quot_bv_signed

val mod_vec_int  : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val quot_vec_int : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
Definition mod_vec_int  := mod_bv_int
Definition quot_vec_int := quot_bv_int

val replicate_bits : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
Fixpoint replicate_bits_aux {a} (w : Word.word a) (n : nat) : Word.word (n * a) :=
match n with
| O => Word.WO
| S m => Word.combine w (replicate_bits_aux w m)
end.
Lemma replicate_ok {n a} `{ArithFact (n >=? 0)} `{ArithFact (a >=? 0)} :
   Z.of_nat (Z.to_nat n * Z.to_nat a) = a * n.
destruct H. destruct H0. unbool_comparisons.
rewrite <- Z2Nat.id. 2: solve [ auto with zarith ].
rewrite Z2Nat.inj_mul. 2,3: solve [ auto with zarith ].
rewrite Nat.mul_comm. reflexivity.
Qed.
Definition replicate_bits {a} (w : mword a) (n : Z) `{ArithFact (n >=? 0)} : mword (a * n) :=
 cast_to_mword (replicate_bits_aux (get_word w) (Z.to_nat n)) replicate_ok.

(*val duplicate : forall 'a. Size 'a => bitU -> integer -> mword 'a
Definition duplicate := duplicate_bit_bv

val eq_vec    : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val neq_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val ult_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val slt_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val ugt_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val sgt_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val ulteq_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val slteq_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val ugteq_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> bool
val sgteq_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> bool*)
Definition eq_vec  {n} (x : mword n) (y : mword n) : bool := Word.weqb (get_word x) (get_word y).
Definition neq_vec {n} (x : mword n) (y : mword n) : bool := negb (eq_vec x y).
(*Definition ult_vec   := ult_bv.
Definition slt_vec   := slt_bv.
Definition ugt_vec   := ugt_bv.
Definition sgt_vec   := sgt_bv.
Definition ulteq_vec := ulteq_bv.
Definition slteq_vec := slteq_bv.
Definition ugteq_vec := ugteq_bv.
Definition sgteq_vec := sgteq_bv.

*)
Lemma eq_vec_true_iff {n} (v w : mword n) :
  eq_vec v w = true <-> v = w.
unfold eq_vec.
destruct n.
* simpl in v,w. shatter_word v. shatter_word w.
  compute. intuition.
* simpl in *. destruct (weq v w).
  + subst. rewrite weqb_eq; tauto.
  + rewrite weqb_ne; auto. split; congruence.
* destruct v.
Qed.

Lemma eq_vec_false_iff {n} (v w : mword n) :
  eq_vec v w = false <-> v <> w.
specialize (eq_vec_true_iff v w).
destruct (eq_vec v w).
intuition.
intros [H1 H2].
split.
* intros _ EQ. intuition.
* auto.
Qed.

Definition eq_vec_dec {n} : forall (x y : mword n), {x = y} + {x <> y}.
refine (match n with
| Z0 => _
| Zpos m => _
| Zneg m => _
end).
* simpl. apply Word.weq.
* simpl. apply Word.weq.
* simpl. destruct x.
Defined.

Instance Decidable_eq_mword {n} : forall (x y : mword n), Decidable (x = y) :=
  Decidable_eq_from_dec eq_vec_dec.

Program Fixpoint reverse_endianness_word {n} (bits : word n) : word n :=
  match n with
  | S (S (S (S (S (S (S (S m))))))) =>
    combine
      (reverse_endianness_word (split2 8 m bits))
      (split1 8 m bits)
  | _ => bits
  end.
Next Obligation.
lia.
Qed.

Definition reverse_endianness {n} (bits : mword n) := with_word (P := id) reverse_endianness_word bits.

Definition get_slice_int {a} `{ArithFact (a >=? 0)} : Z -> Z -> Z -> mword a := get_slice_int_bv.

Definition set_slice n m (v : mword n) x (w : mword m) : mword n :=
  update_subrange_vec_dec_unchecked v (x + m - 1) x w.

Definition set_slice_int len n lo (v : mword len) : Z :=
  let hi := lo + len - 1 in
  (* We don't currently have a constraint on lo in the sail prelude, so let's
     avoid one here. *)
  if sumbool_of_bool (Z.gtb hi 0) then
    let bs : mword (hi + 1) := mword_of_int n in
    (int_of_mword true (update_subrange_vec_dec_unchecked bs hi lo v))
  else n.

(* Variant of bitvector slicing for the ARM model with few constraints *)
Definition slice {m} (v : mword m) lo len `{ArithFact (0 <=? len)} : mword len :=
  if sumbool_of_bool (orb (len =? 0) (lo <? 0))
  then zeros len
  else
    if sumbool_of_bool (lo + len - 1 >=? m)
    then if sumbool_of_bool (lo <? m)
         then zero_extend (subrange_vec_dec v (m - 1) lo) len
         else zeros len
    else autocast (subrange_vec_dec v (lo + len - 1) lo).

Lemma slice_is_ok m (v : mword m) lo len
                  (H1 : 0 <= lo) (H2 : 0 < len) (H3: lo + len < m) :
  slice v lo len = autocast (subrange_vec_dec v (lo + len - 1) lo).
unfold slice.
destruct (sumbool_of_bool _).
* exfalso.
  unbool_comparisons.
  lia.
* destruct (sumbool_of_bool _).
  + exfalso.
    unbool_comparisons.  
    lia.
  + repeat replace_ArithFact_proof.
    reflexivity.
Qed.

Import ListNotations.
Definition count_leading_zeros {N : Z} (x : mword N) `{ArithFact (N >=? 1)} 
: {n : Z & ArithFact (0 <=? n <=? N)} :=
  let r : {n : Z & ArithFact (0 <=? n <=? N)} := build_ex N in
  foreach_Z_up 0 (N - 1) 1 r
    (fun i _ r =>
      (if ((eq_vec (vec_of_bits [access_vec_dec x i]  : mword 1) (vec_of_bits [B1]  : mword 1)))
       then build_ex
            (Z.sub (Z.sub (length_mword x) i) 1)
             : {n : Z & ArithFact (0 <=? n <=? N)}
       else r))
   .

Definition prerr_bits {a} (s : string) (bs : mword a) : unit := tt.
Definition print_bits {a} (s : string) (bs : mword a) : unit := tt.
