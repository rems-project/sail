Require Import Sail_values.
Require Import Sail_operators.
Require Import Prompt_monad.
Require Import Prompt.
Require bbv.Word.
Require Import Arith.
Require Import Omega.

Definition cast_mword {m n} (x : mword m) (eq : m = n) : mword n.
rewrite <- eq.
exact x.
Defined.

Definition cast_word {m n} (x : Word.word m) (eq : m = n) : Word.word n.
rewrite <- eq.
exact x.
Defined.

Definition mword_of_nat {m} (x : Word.word m) : mword (Z.of_nat m).
destruct m.
- exact x.
- simpl. rewrite SuccNat2Pos.id_succ. exact x.
Defined.

Definition cast_to_mword {m n} (x : Word.word m) (eq : Z.of_nat m = n) : mword n.
destruct n.
- constructor.
- rewrite <- eq. exact (mword_of_nat x).
- exfalso. destruct m; simpl in *; congruence.
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

(*val subrange_vec_inc : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b*)
(* TODO: get rid of bogus default *)
Parameter dummy_vector : forall {n} `{ArithFact (n >= 0)}, mword n.
Definition subrange_vec_inc {a b} `{ArithFact (b >= 0)} (w: mword a) i j : mword b :=
  opt_def dummy_vector (of_bits (subrange_bv_inc w i j)).

(*val subrange_vec_dec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b*)
(* TODO: get rid of bogus default *)
Definition subrange_vec_dec {n m} `{ArithFact (m >= 0)} (w : mword n) i j :mword m :=
  opt_def dummy_vector (of_bits (subrange_bv_dec w i j)).

(*val update_subrange_vec_inc : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
Definition update_subrange_vec_inc {a b} (v : mword a) i j (w : mword b) : mword a :=
  opt_def dummy_vector (of_bits (update_subrange_bv_inc v i j w)).

(*val update_subrange_vec_dec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
Definition update_subrange_vec_dec {a b} (v : mword a) i j (w : mword b) : mword a :=
  opt_def dummy_vector (of_bits (update_subrange_bv_dec v i j w)).

Lemma mword_nonneg {a} : mword a -> a >= 0.
destruct a;
auto using Z.le_ge, Zle_0_pos with zarith.
destruct 1.
Qed.

(*val extz_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition extz_vec {a b} `{ArithFact (b >= a)} (n : Z) (v : mword a) : mword b.
refine (cast_to_mword (Word.zext (get_word v) (Z.to_nat (b - a))) _).
unwrap_ArithFacts.
assert (a >= 0). { apply mword_nonneg. assumption. }
rewrite <- Z2Nat.inj_add; try omega.
rewrite Zplus_minus.
apply Z2Nat.id.
auto with zarith.
Defined.

(*val exts_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition exts_vec {a b} `{ArithFact (b >= a)} (n : Z) (v : mword a) : mword b.
refine (cast_to_mword (Word.sext (get_word v) (Z.to_nat (b - a))) _).
unwrap_ArithFacts.
assert (a >= 0). { apply mword_nonneg. assumption. }
rewrite <- Z2Nat.inj_add; try omega.
rewrite Zplus_minus.
apply Z2Nat.id.
auto with zarith.
Defined.

Definition zero_extend {a} (v : mword a) (n : Z) `{ArithFact (n >= a)} : mword n := extz_vec n v.

Definition sign_extend {a} (v : mword a) (n : Z) `{ArithFact (n >= a)} : mword n := exts_vec n v.

Lemma truncate_eq {m n} : m >= 0 -> m <= n -> (Z.to_nat n = Z.to_nat m + (Z.to_nat n - Z.to_nat m))%nat.
intros.
assert ((Z.to_nat m <= Z.to_nat n)%nat).
{ apply Z2Nat.inj_le; omega. }
omega.
Qed.

Definition vector_truncate {n} (v : mword n) (m : Z) `{ArithFact (m >= 0)} `{ArithFact (m <= n)} : mword m :=
  cast_to_mword (Word.split1 _ _ (cast_word (get_word v) (ltac:(unwrap_ArithFacts; apply truncate_eq; auto) : Z.to_nat n = Z.to_nat m + (Z.to_nat n - Z.to_nat m))%nat)) (ltac:(unwrap_ArithFacts; apply Z2Nat.id; omega) : Z.of_nat (Z.to_nat m) = m).

Lemma concat_eq {a b} : a >= 0 -> b >= 0 -> Z.of_nat (Z.to_nat b + Z.to_nat a)%nat = a + b.
intros.
rewrite Nat2Z.inj_add.
rewrite Z2Nat.id; auto with zarith.
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

Lemma length_list_pos : forall {A} {l:list A}, length_list l >= 0.
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

val string_of_vec : forall 'a. Size 'a => mword 'a -> string
Definition string_of_vec := string_of_bv*)
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
Definition mult_vec  {n} : mword n -> mword n -> mword n := word_binop Word.wmult.
(*Definition smult_vec {n} : mword n -> mword n -> mword n := smult_bv w.*)

(*val add_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val sadd_vec_int  : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val sub_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a
val mult_vec_int  : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b
val smult_vec_int : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
(*Definition add_vec_int   {a} (w : mword a) : Z -> mword a := add_bv_int w.
Definition sadd_vec_int  {a} (w : mword a) : Z -> mword a := sadd_bv_int w.
Definition sub_vec_int   {a} (w : mword a) : Z -> mword a := sub_bv_int w.*)
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
Definition shiftl       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wlshift w (Z.to_nat n)) v.
Definition shiftr       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wrshift w (Z.to_nat n)) v.
Definition arith_shiftr {a} (v : mword a) n : mword a := with_word (P := id) (fun w => Word.wrshifta w (Z.to_nat n)) v.
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
Lemma replicate_ok {n a} `{ArithFact (n >= 0)} `{ArithFact (a >= 0)} :
   Z.of_nat (Z.to_nat n * Z.to_nat a) = n * a.
destruct H. destruct H0.
rewrite <- Z2Nat.id; auto with zarith.
rewrite Z2Nat.inj_mul; auto with zarith.
Qed.
Definition replicate_bits {a} (w : mword a) (n : Z) `{ArithFact (n >= 0)} : mword (n * a) :=
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

Definition get_slice_int {a} `{ArithFact (a >= 0)} : Z -> Z -> Z -> mword a := get_slice_int_bv.
