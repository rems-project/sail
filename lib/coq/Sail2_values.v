(* Version of sail_values.lem that uses Lems machine words library *)

(*Require Import Sail_impl_base*)
Require Export ZArith.
Require Export String.
Require Import bbv.Word.
Require Export List.
Require Export Sumbool.
Require Export DecidableClass.
Import ListNotations.

Open Scope Z.

(* Constraint solving basics.  A HintDb which unfolding hints and lemmata
   can be added to, and a typeclass to wrap constraint arguments in to
   trigger automatic solving. *)
Create HintDb sail.
Class ArithFact (P : Prop) := { fact : P }.
Lemma use_ArithFact {P} `(ArithFact P) : P.
apply fact.
Defined.

Definition build_ex (n:Z) {P:Z -> Prop} `{H:ArithFact (P n)} : {x : Z & ArithFact (P x)} :=
  existT _ n H.

Definition generic_eq {T:Type} (x y:T) `{Decidable (x = y)} := Decidable_witness.
Definition generic_neq {T:Type} (x y:T) `{Decidable (x = y)} := negb Decidable_witness.
Lemma generic_eq_true {T} {x y:T} `{Decidable (x = y)} : generic_eq x y = true -> x = y.
apply Decidable_spec.
Qed.
Lemma generic_eq_false {T} {x y:T} `{Decidable (x = y)} : generic_eq x y = false -> x <> y.
unfold generic_eq.
intros H1 H2.
rewrite <- Decidable_spec in H2.
congruence.
Qed.
Lemma generic_neq_true {T} {x y:T} `{Decidable (x = y)} : generic_neq x y = true -> x <> y.
unfold generic_neq.
intros H1 H2.
rewrite <- Decidable_spec in H2.
destruct Decidable_witness; simpl in *; 
congruence.
Qed.
Lemma generic_neq_false {T} {x y:T} `{Decidable (x = y)} : generic_neq x y = false -> x = y.
unfold generic_neq.
intro H1.
rewrite <- Decidable_spec.
destruct Decidable_witness; simpl in *; 
congruence.
Qed.
Instance Decidable_eq_from_dec {T:Type} (eqdec: forall x y : T, {x = y} + {x <> y}) : 
  forall (x y : T), Decidable (eq x y) := {
  Decidable_witness := proj1_sig (bool_of_sumbool (eqdec x y))
}.
destruct (eqdec x y); simpl; split; congruence.
Qed.


(* Project away range constraints in comparisons *)
Definition ltb_range_l {P} (l : sigT P) r := Z.ltb (projT1 l) r.
Definition leb_range_l {P} (l : sigT P) r := Z.leb (projT1 l) r.
Definition gtb_range_l {P} (l : sigT P) r := Z.gtb (projT1 l) r.
Definition geb_range_l {P} (l : sigT P) r := Z.geb (projT1 l) r.
Definition ltb_range_r {P} l (r : sigT P) := Z.ltb l (projT1 r).
Definition leb_range_r {P} l (r : sigT P) := Z.leb l (projT1 r).
Definition gtb_range_r {P} l (r : sigT P) := Z.gtb l (projT1 r).
Definition geb_range_r {P} l (r : sigT P) := Z.geb l (projT1 r).

Definition ii := Z.
Definition nn := nat.

(*val pow : Z -> Z -> Z*)
Definition pow m n := m ^ n.

Definition pow2 n := pow 2 n.
(*
Definition inline lt := (<)
Definition inline gt := (>)
Definition inline lteq := (<=)
Definition inline gteq := (>=)

val eq : forall a. Eq a => a -> a -> bool
Definition inline eq l r := (l = r)

val neq : forall a. Eq a => a -> a -> bool*)
Definition neq l r := (negb (l =? r)). (* Z only *)

(*let add_int l r := integerAdd l r
Definition add_signed l r := integerAdd l r
Definition sub_int l r := integerMinus l r
Definition mult_int l r := integerMult l r
Definition div_int l r := integerDiv l r
Definition div_nat l r := natDiv l r
Definition power_int_nat l r := integerPow l r
Definition power_int_int l r := integerPow l (Z.to_nat r)
Definition negate_int i := integerNegate i
Definition min_int l r := integerMin l r
Definition max_int l r := integerMax l r

Definition add_real l r := realAdd l r
Definition sub_real l r := realMinus l r
Definition mult_real l r := realMult l r
Definition div_real l r := realDiv l r
Definition negate_real r := realNegate r
Definition abs_real r := realAbs r
Definition power_real b e := realPowInteger b e*)

Definition print_int (_ : string) (_ : Z) : unit := tt.

(*
Definition or_bool l r := (l || r)
Definition and_bool l r := (l && r)
Definition xor_bool l r := xor l r
*)
Definition append_list {A:Type} (l : list A) r := l ++ r.
Definition length_list {A:Type} (xs : list A) := Z.of_nat (List.length xs).
Definition take_list {A:Type} n (xs : list A) := firstn (Z.to_nat n) xs.
Definition drop_list {A:Type} n (xs : list A) := skipn (Z.to_nat n) xs.
(*
val repeat : forall a. list a -> Z -> list a*)
Fixpoint repeat' {a} (xs : list a) n :=
  match n with
  | O => []
  | S n => xs ++ repeat' xs n
  end.
Definition repeat {a} (xs : list a) (n : Z) :=
  if n <=? 0 then []
  else repeat' xs (Z.to_nat n).
(*declare {isabelle} termination_argument repeat = automatic

Definition duplicate_to_list bit length := repeat [bit] length

Fixpoint replace bs (n : Z) b' := match bs with
  | [] => []
  | b :: bs =>
     if n = 0 then b' :: bs
              else b :: replace bs (n - 1) b'
  end
declare {isabelle} termination_argument replace = automatic

Definition upper n := n

(* Modulus operation corresponding to quot below -- result
   has sign of dividend. *)
Definition hardware_mod (a: Z) (b:Z) : Z :=
  let m := (abs a) mod (abs b) in
  if a < 0 then ~m else m

(* There are different possible answers for integer divide regarding
rounding behaviour on negative operands. Positive operands always
round down so derive the one we want (trucation towards zero) from
that *)
Definition hardware_quot (a:Z) (b:Z) : Z :=
  let q := (abs a) / (abs b) in
  if ((a<0) = (b<0)) then
    q  (* same sign -- result positive *)
  else
    ~q (* different sign -- result negative *)

Definition max_64u := (integerPow 2 64) - 1
Definition max_64  := (integerPow 2 63) - 1
Definition min_64  := 0 - (integerPow 2 63)
Definition max_32u := (4294967295 : Z)
Definition max_32  := (2147483647 : Z)
Definition min_32  := (0 - 2147483648 : Z)
Definition max_8   := (127 : Z)
Definition min_8   := (0 - 128 : Z)
Definition max_5   := (31 : Z)
Definition min_5   := (0 - 32 : Z)
*)

(* just_list takes a list of maybes and returns Some xs if all elements have
   a value, and None if one of the elements is None. *)
(*val just_list : forall a. list (option a) -> option (list a)*)
Fixpoint just_list {A} (l : list (option A)) := match l with
  | [] => Some []
  | (x :: xs) =>
    match (x, just_list xs) with
      | (Some x, Some xs) => Some (x :: xs)
      | (_, _) => None
    end
  end.
(*declare {isabelle} termination_argument just_list = automatic

lemma just_list_spec:
  ((forall xs. (just_list xs = None) <-> List.elem None xs) &&
   (forall xs es. (just_list xs = Some es) <-> (xs = List.map Some es)))*)

(*** Bits *)
Inductive bitU := B0 | B1 | BU.

Definition showBitU b :=
match b with
  | B0 => "O"
  | B1 => "I"
  | BU => "U"
end%string.

(*instance (Show bitU)
  let show := showBitU
end*)

Class BitU (a : Type) : Type := {
  to_bitU : a -> bitU;
  of_bitU : bitU -> a
}.

Instance bitU_BitU : (BitU bitU) := {
  to_bitU b := b;
  of_bitU b := b
}.

Definition bool_of_bitU bu := match bu with
  | B0 => Some false
  | B1 => Some true
  | BU => None
  end.

Definition bitU_of_bool (b : bool) := if b then B1 else B0.

(*Instance bool_BitU : (BitU bool) := {
  to_bitU := bitU_of_bool;
  of_bitU := bool_of_bitU
}.*)

Definition cast_bit_bool := bool_of_bitU.
(*
Definition bit_lifted_of_bitU bu := match bu with
  | B0 => Bitl_zero
  | B1 => Bitl_one
  | BU => Bitl_undef
  end.

Definition bitU_of_bit := function
  | Bitc_zero => B0
  | Bitc_one  => B1
  end.

Definition bit_of_bitU := function
  | B0 => Bitc_zero
  | B1 => Bitc_one
  | BU => failwith "bit_of_bitU: BU"
  end.

Definition bitU_of_bit_lifted := function
  | Bitl_zero => B0
  | Bitl_one  => B1
  | Bitl_undef => BU
  | Bitl_unknown => failwith "bitU_of_bit_lifted Bitl_unknown"
  end.
*)
Definition not_bit b :=
match b with
  | B1 => B0
  | B0 => B1
  | BU => BU
  end.

(*val is_one : Z -> bitU*)
Definition is_one (i : Z) :=
  if i =? 1 then B1 else B0.

Definition binop_bit op x y :=
  match (x, y) with
  | (BU,_) => BU (*Do we want to do this or to respect | of I and & of B0 rules?*)
  | (_,BU) => BU (*Do we want to do this or to respect | of I and & of B0 rules?*)
  | (x,y) => bitU_of_bool (op (bool_of_bitU x) (bool_of_bitU y))
  end.

(*val and_bit : bitU -> bitU -> bitU
Definition and_bit := binop_bit (&&)

val or_bit : bitU -> bitU -> bitU
Definition or_bit := binop_bit (||)

val xor_bit : bitU -> bitU -> bitU
Definition xor_bit := binop_bit xor

val (&.) : bitU -> bitU -> bitU
Definition inline (&.) x y := and_bit x y

val (|.) : bitU -> bitU -> bitU
Definition inline (|.) x y := or_bit x y

val (+.) : bitU -> bitU -> bitU
Definition inline (+.) x y := xor_bit x y
*)

(*** Bool lists ***)

(*val bools_of_nat_aux : integer -> natural -> list bool -> list bool*)
Fixpoint bools_of_nat_aux len (x : nat) (acc : list bool) : list bool :=
  match len with
  | O => acc
  | S len' => bools_of_nat_aux len' (x / 2) ((if x mod 2 =? 1 then true else false) :: acc)
  end %nat.
  (*else (if x mod 2 = 1 then true else false) :: bools_of_nat_aux (x / 2)*)
(*declare {isabelle} termination_argument bools_of_nat_aux = automatic*)
Definition bools_of_nat len n := bools_of_nat_aux (Z.to_nat len) n [] (*List.reverse (bools_of_nat_aux n)*).

(*val nat_of_bools_aux : natural -> list bool -> natural*)
Fixpoint nat_of_bools_aux (acc : nat) (bs : list bool) : nat :=
  match bs with
  | [] => acc
  | true :: bs => nat_of_bools_aux ((2 * acc) + 1) bs
  | false :: bs => nat_of_bools_aux (2 * acc) bs
end.
(*declare {isabelle; hol} termination_argument nat_of_bools_aux = automatic*)
Definition nat_of_bools bs := nat_of_bools_aux 0 bs.

(*val unsigned_of_bools : list bool -> integer*)
Definition unsigned_of_bools bs := Z.of_nat (nat_of_bools bs).

(*val signed_of_bools : list bool -> integer*)
Definition signed_of_bools bs :=
  match bs with
    | true :: _  => 0 - (1 + (unsigned_of_bools (List.map negb bs)))
    | false :: _ => unsigned_of_bools bs
    | [] => 0 (* Treat empty list as all zeros *)
  end.

(*val int_of_bools : bool -> list bool -> integer*)
Definition int_of_bools (sign : bool) bs := if sign then signed_of_bools bs else unsigned_of_bools bs.

(*val pad_list : forall 'a. 'a -> list 'a -> integer -> list 'a*)
Fixpoint pad_list_nat {a} (x : a) (xs : list a) n :=
  match n with
  | O => xs
  | S n' => pad_list_nat x (x :: xs) n'
  end.
(*declare {isabelle} termination_argument pad_list = automatic*)
Definition pad_list {a} x xs n := @pad_list_nat a x xs (Z.to_nat n).

Definition ext_list {a} pad len (xs : list a) :=
  let longer := len - (Z.of_nat (List.length xs)) in
  if longer <? 0 then skipn (Z.abs_nat (longer)) xs
  else pad_list pad xs longer.

(*let extz_bools len bs = ext_list false len bs*)
Definition exts_bools len bs :=
  match bs with
    | true :: _ => ext_list true len bs
    | _ => ext_list false len bs
  end.

Fixpoint add_one_bool_ignore_overflow_aux bits := match bits with
  | [] => []
  | false :: bits => true :: bits
  | true :: bits => false :: add_one_bool_ignore_overflow_aux bits
end.
(*declare {isabelle; hol} termination_argument add_one_bool_ignore_overflow_aux = automatic*)

Definition add_one_bool_ignore_overflow bits :=
  List.rev (add_one_bool_ignore_overflow_aux (List.rev bits)).

(*let bool_list_of_int n =
  let bs_abs = false :: bools_of_nat (naturalFromInteger (abs n)) in
  if n >= (0 : integer) then bs_abs
  else add_one_bool_ignore_overflow (List.map not bs_abs)
let bools_of_int len n = exts_bools len (bool_list_of_int n)*)
Definition bools_of_int len n :=
  let bs_abs := bools_of_nat len (Z.abs_nat n) in
  if n >=? 0 then bs_abs
  else add_one_bool_ignore_overflow (List.map negb bs_abs).

(*** Bit lists ***)

(*val bits_of_nat_aux : natural -> list bitU*)
Fixpoint bits_of_nat_aux n x :=
  match n,x with
  | O,_ => []
  | _,O => []
  | S n, S _ => (if x mod 2 =? 1 then B1 else B0) :: bits_of_nat_aux n (x / 2)
  end%nat.
(**declare {isabelle} termination_argument bits_of_nat_aux = automatic*)
Definition bits_of_nat n := List.rev (bits_of_nat_aux n n).

(*val nat_of_bits_aux : natural -> list bitU -> natural*)
Fixpoint nat_of_bits_aux acc bs := match bs with
  | [] => Some acc
  | B1 :: bs => nat_of_bits_aux ((2 * acc) + 1) bs
  | B0 :: bs => nat_of_bits_aux (2 * acc) bs
  | BU :: bs => None
end%nat.
(*declare {isabelle} termination_argument nat_of_bits_aux = automatic*)
Definition nat_of_bits bits := nat_of_bits_aux 0 bits.

Definition not_bits := List.map not_bit.

Definition binop_bits op bsl bsr :=
  List.fold_right (fun '(bl, br) acc => binop_bit op bl br :: acc) [] (List.combine bsl bsr).
(*
Definition and_bits := binop_bits (&&)
Definition or_bits := binop_bits (||)
Definition xor_bits := binop_bits xor

val unsigned_of_bits : list bitU -> Z*)
Definition unsigned_of_bits bits :=
match just_list (List.map bool_of_bitU bits) with
| Some bs => Some (unsigned_of_bools bs)
| None => None
end.

(*val signed_of_bits : list bitU -> Z*)
Definition signed_of_bits bits :=
  match just_list (List.map bool_of_bitU bits) with
  | Some bs => Some (signed_of_bools bs)
  | None => None
  end.

(*val int_of_bits : bool -> list bitU -> maybe integer*)
Definition int_of_bits (sign : bool) bs :=
 if sign then signed_of_bits bs else unsigned_of_bits bs.

(*val pad_bitlist : bitU -> list bitU -> Z -> list bitU*)
Fixpoint pad_bitlist_nat (b : bitU) bits n :=
match n with
| O => bits
| S n' => pad_bitlist_nat b (b :: bits) n'
end.
Definition pad_bitlist b bits n := pad_bitlist_nat b bits (Z.to_nat n). (* Negative n will come out as 0 *)
(*  if n <= 0 then bits else pad_bitlist b (b :: bits) (n - 1).
declare {isabelle} termination_argument pad_bitlist = automatic*)

Definition ext_bits pad len bits :=
  let longer := len - (Z.of_nat (List.length bits)) in
  if longer <? 0 then skipn (Z.abs_nat longer) bits
  else pad_bitlist pad bits longer.

Definition extz_bits len bits := ext_bits B0 len bits.
Parameter undefined_list_bitU : list bitU.
Definition exts_bits len bits :=
  match bits with
  | BU :: _ => undefined_list_bitU (*failwith "exts_bits: undefined bit"*)
  | B1 :: _ => ext_bits B1 len bits
  | _ => ext_bits B0 len bits
  end.

Fixpoint add_one_bit_ignore_overflow_aux bits := match bits with
  | [] => []
  | B0 :: bits => B1 :: bits
  | B1 :: bits => B0 :: add_one_bit_ignore_overflow_aux bits
  | BU :: _ => undefined_list_bitU (*failwith "add_one_bit_ignore_overflow: undefined bit"*)
end.
(*declare {isabelle} termination_argument add_one_bit_ignore_overflow_aux = automatic*)

Definition add_one_bit_ignore_overflow bits :=
  rev (add_one_bit_ignore_overflow_aux (rev bits)).

Definition bitlist_of_int n :=
  let bits_abs := B0 :: bits_of_nat (Z.abs_nat n) in
  if n >=? 0 then bits_abs
  else add_one_bit_ignore_overflow (not_bits bits_abs).

Definition bits_of_int len n := exts_bits len (bitlist_of_int n).

(*val arith_op_bits :
  (integer -> integer -> integer) -> bool -> list bitU -> list bitU -> list bitU*)
Definition arith_op_bits (op : Z -> Z -> Z) (sign : bool) l r :=
  match (int_of_bits sign l, int_of_bits sign r) with
    | (Some li, Some ri) => bits_of_int (length_list l) (op li ri)
    | (_, _) => repeat [BU] (length_list l)
  end.


(*
Definition char_of_nibble := function
  | (B0, B0, B0, B0) => Some #'0'
  | (B0, B0, B0, B1) => Some #'1'
  | (B0, B0, B1, B0) => Some #'2'
  | (B0, B0, B1, B1) => Some #'3'
  | (B0, B1, B0, B0) => Some #'4'
  | (B0, B1, B0, B1) => Some #'5'
  | (B0, B1, B1, B0) => Some #'6'
  | (B0, B1, B1, B1) => Some #'7'
  | (B1, B0, B0, B0) => Some #'8'
  | (B1, B0, B0, B1) => Some #'9'
  | (B1, B0, B1, B0) => Some #'A'
  | (B1, B0, B1, B1) => Some #'B'
  | (B1, B1, B0, B0) => Some #'C'
  | (B1, B1, B0, B1) => Some #'D'
  | (B1, B1, B1, B0) => Some #'E'
  | (B1, B1, B1, B1) => Some #'F'
  | _ => None
  end

Fixpoint hexstring_of_bits bs := match bs with
  | b1 :: b2 :: b3 :: b4 :: bs =>
     let n := char_of_nibble (b1, b2, b3, b4) in
     let s := hexstring_of_bits bs in
     match (n, s) with
     | (Some n, Some s) => Some (n :: s)
     | _ => None
     end
  | _ => None
  end
declare {isabelle} termination_argument hexstring_of_bits = automatic

Definition show_bitlist bs :=
  match hexstring_of_bits bs with
  | Some s => toString (#'0' :: #x' :: s)
  | None => show bs
  end

(*** List operations *)

Definition inline (^^) := append_list

val subrange_list_inc : forall a. list a -> Z -> Z -> list a*)
Definition subrange_list_inc {A} (xs : list A) i j :=
  let toJ := firstn (Z.to_nat j + 1) xs in
  let fromItoJ := skipn (Z.to_nat i) toJ in
  fromItoJ.

(*val subrange_list_dec : forall a. list a -> Z -> Z -> list a*)
Definition subrange_list_dec {A} (xs : list A) i j :=
  let top := (length_list xs) - 1 in
  subrange_list_inc xs (top - i) (top - j).

(*val subrange_list : forall a. bool -> list a -> Z -> Z -> list a*)
Definition subrange_list {A} (is_inc : bool) (xs : list A) i j :=
 if is_inc then subrange_list_inc xs i j else subrange_list_dec xs i j.

Definition splitAt {A} n (l : list A) := (firstn n l, skipn n l).

(*val update_subrange_list_inc : forall a. list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list_inc {A} (xs : list A) i j xs' :=
  let (toJ,suffix) := splitAt (Z.to_nat j + 1) xs in
  let (prefix,_fromItoJ) := splitAt (Z.to_nat i) toJ in
  prefix ++ xs' ++ suffix.

(*val update_subrange_list_dec : forall a. list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list_dec {A} (xs : list A) i j xs' :=
  let top := (length_list xs) - 1 in
  update_subrange_list_inc xs (top - i) (top - j) xs'.

(*val update_subrange_list : forall a. bool -> list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list {A} (is_inc : bool) (xs : list A) i j xs' :=
  if is_inc then update_subrange_list_inc xs i j xs' else update_subrange_list_dec xs i j xs'.

Open Scope nat.
Fixpoint nth_in_range {A} (n:nat) (l:list A) : n < length l -> A.
refine 
  (match n, l with
  | O, h::_ => fun _ => h
  | S m, _::t => fun H => nth_in_range A m t _
  | _,_ => fun H => _
  end).
exfalso. inversion H.
exfalso. inversion H.
simpl in H. omega.
Defined.

Lemma nth_in_range_is_nth : forall A n (l : list A) d (H : n < length l),
  nth_in_range n l H = nth n l d.
intros until d. revert n.
induction l; intros n H.
* inversion H.
* destruct n.
  + reflexivity.
  + apply IHl.
Qed.

Lemma nth_Z_nat {A} {n} {xs : list A} :
  (0 <= n)%Z -> (n < length_list xs)%Z -> Z.to_nat n < length xs.
unfold length_list.
intros nonneg bounded.
rewrite Z2Nat.inj_lt in bounded; auto using Zle_0_nat.
rewrite Nat2Z.id in bounded.
assumption.
Qed.

(*
Lemma nth_top_aux {A} {n} {xs : list A} : Z.to_nat n < length xs -> let top := ((length_list xs) - 1)%Z in Z.to_nat (top - n)%Z < length xs.
unfold length_list.
generalize (length xs).
intro n0.
rewrite <- (Nat2Z.id n0).
intro H.
apply Z2Nat.inj_lt.
* omega. 
*)

Close Scope nat.

(*val access_list_inc : forall a. list a -> Z -> a*)
Definition access_list_inc {A} (xs : list A) n `{ArithFact (0 <= n)} `{ArithFact (n < length_list xs)} := nth_in_range (Z.to_nat n) xs (nth_Z_nat (use_ArithFact _) (use_ArithFact _)).

(*val access_list_dec : forall a. list a -> Z -> a*)
Definition access_list_dec {A} (xs : list A) n `{ArithFact (0 <= n)} `{ArithFact (n < length_list xs)} : A.
refine (
  let top := (length_list xs) - 1 in
  @access_list_inc A xs (top - n) _ _).
constructor. apply use_ArithFact in H. apply use_ArithFact in H0. omega.
constructor. apply use_ArithFact in H. apply use_ArithFact in H0. omega.
Defined.

(*val access_list : forall a. bool -> list a -> Z -> a*)
Definition access_list {A} (is_inc : bool) (xs : list A) n `{ArithFact (0 <= n)} `{ArithFact (n < length_list xs)} :=
  if is_inc then access_list_inc xs n else access_list_dec xs n.

Definition access_list_opt_inc {A} (xs : list A) n := nth_error xs (Z.to_nat n).

(*val access_list_dec : forall a. list a -> Z -> a*)
Definition access_list_opt_dec {A} (xs : list A) n :=
  let top := (length_list xs) - 1 in
  access_list_opt_inc xs (top - n).

(*val access_list : forall a. bool -> list a -> Z -> a*)
Definition access_list_opt {A} (is_inc : bool) (xs : list A) n :=
  if is_inc then access_list_opt_inc xs n else access_list_opt_dec xs n.

Definition list_update {A} (xs : list A) n x := firstn n xs ++ x :: skipn (S n) xs.

(*val update_list_inc : forall a. list a -> Z -> a -> list a*)
Definition update_list_inc {A} (xs : list A) n x := list_update xs (Z.to_nat n) x.

(*val update_list_dec : forall a. list a -> Z -> a -> list a*)
Definition update_list_dec {A} (xs : list A) n x :=
  let top := (length_list xs) - 1 in
  update_list_inc xs (top - n) x.

(*val update_list : forall a. bool -> list a -> Z -> a -> list a*)
Definition update_list {A} (is_inc : bool) (xs : list A) n x :=
  if is_inc then update_list_inc xs n x else update_list_dec xs n x.

(*Definition extract_only_element := function
  | [] => failwith "extract_only_element called for empty list"
  | [e] => e
  | _ => failwith "extract_only_element called for list with more elements"
end

(*** Machine words *)
*)
Definition mword (n : Z) :=
  match n with
  | Zneg _ => False
  | Z0 => word 0
  | Zpos p => word (Pos.to_nat p)
  end.

Definition get_word {n} : mword n -> word (Z.to_nat n) :=
  match n with
  | Zneg _ => fun x => match x with end
  | Z0 => fun x => x
  | Zpos p => fun x => x
  end.

Definition with_word {n} {P : Type -> Type} : (word (Z.to_nat n) -> P (word (Z.to_nat n))) -> mword n -> P (mword n) :=
match n with
| Zneg _ => fun f w => match w with end
| Z0 => fun f w => f w
| Zpos _ => fun f w => f w
end.

Program Definition to_word {n} : n >= 0 -> word (Z.to_nat n) -> mword n :=
  match n with
  | Zneg _ => fun H _ => _
  | Z0 => fun _ w => w
  | Zpos _ => fun _ w => w
  end.

(*val length_mword : forall a. mword a -> Z*)
Definition length_mword {n} (w : mword n) := n.

(*val slice_mword_dec : forall a b. mword a -> Z -> Z -> mword b*)
(*Definition slice_mword_dec w i j := word_extract (Z.to_nat i) (Z.to_nat j) w.

val slice_mword_inc : forall a b. mword a -> Z -> Z -> mword b
Definition slice_mword_inc w i j :=
  let top := (length_mword w) - 1 in
  slice_mword_dec w (top - i) (top - j)

val slice_mword : forall a b. bool -> mword a -> Z -> Z -> mword b
Definition slice_mword is_inc w i j := if is_inc then slice_mword_inc w i j else slice_mword_dec w i j

val update_slice_mword_dec : forall a b. mword a -> Z -> Z -> mword b -> mword a
Definition update_slice_mword_dec w i j w' := word_update w (Z.to_nat i) (Z.to_nat j) w'

val update_slice_mword_inc : forall a b. mword a -> Z -> Z -> mword b -> mword a
Definition update_slice_mword_inc w i j w' :=
  let top := (length_mword w) - 1 in
  update_slice_mword_dec w (top - i) (top - j) w'

val update_slice_mword : forall a b. bool -> mword a -> Z -> Z -> mword b -> mword a
Definition update_slice_mword is_inc w i j w' :=
  if is_inc then update_slice_mword_inc w i j w' else update_slice_mword_dec w i j w'

val access_mword_dec : forall a. mword a -> Z -> bitU*)
Parameter undefined_bit : bool.
Definition getBit {n} :=
match n with
| O => fun (w : word O) i => undefined_bit
| S n => fun (w : word (S n)) i => wlsb (wrshift w i)
end.

Definition access_mword_dec {m} (w : mword m) n := bitU_of_bool (getBit (get_word w) (Z.to_nat n)).

(*val access_mword_inc : forall a. mword a -> Z -> bitU*)
Definition access_mword_inc {m} (w : mword m) n :=
  let top := (length_mword w) - 1 in
  access_mword_dec w (top - n).

(*Parameter access_mword : forall {a}, bool -> mword a -> Z -> bitU.*)
Definition access_mword {a} (is_inc : bool) (w : mword a) n :=
  if is_inc then access_mword_inc w n else access_mword_dec w n.

Definition setBit {n} :=
match n with
| O => fun (w : word O) i b => w
| S n => fun (w : word (S n)) i (b : bool) =>
  let bit : word (S n) := wlshift (natToWord _ 1) i in
  let mask : word (S n) := wnot bit in
  let masked := wand mask w in
  if b then masked else wor masked bit
end.

(*val update_mword_bool_dec : forall 'a. mword 'a -> integer -> bool -> mword 'a*)
Definition update_mword_bool_dec {a} (w : mword a) n b : mword a :=
  with_word (P := id) (fun w => setBit w (Z.to_nat n) b) w.
Definition update_mword_dec {a} (w : mword a) n b :=
 match bool_of_bitU b with
 | Some bl => Some (update_mword_bool_dec w n bl)
 | None => None
 end.

(*val update_mword_inc : forall a. mword a -> Z -> bitU -> mword a*)
Definition update_mword_inc {a} (w : mword a) n b :=
  let top := (length_mword w) - 1 in
  update_mword_dec w (top - n) b.

(*Parameter update_mword : forall {a}, bool -> mword a -> Z -> bitU -> mword a.*)
Definition update_mword {a} (is_inc : bool) (w : mword a) n b :=
  if is_inc then update_mword_inc w n b else update_mword_dec w n b.

(*val int_of_mword : forall 'a. bool -> mword 'a -> integer*)
Definition int_of_mword {a} `{ArithFact (a >= 0)} (sign : bool) (w : mword a) :=
  if sign then wordToZ (get_word w) else Z.of_N (wordToN (get_word w)).


(*val mword_of_int : forall a. Size a => Z -> Z -> mword a
Definition mword_of_int len n :=
  let w := wordFromInteger n in
  if (length_mword w = len) then w else failwith "unexpected word length"
*)
Program Definition mword_of_int {len} `{H:ArithFact (len >= 0)} n : mword len :=
match len with
| Zneg _ => _
| Z0 => ZToWord 0 n
| Zpos p => ZToWord (Pos.to_nat p) n
end.
Next Obligation.
destruct H.
auto.
Defined.
(*
(* Translating between a type level number (itself n) and an integer *)

Definition size_itself_int x := Z.of_nat (size_itself x)

(* NB: the corresponding sail type is forall n. atom(n) -> itself(n),
   the actual integer is ignored. *)

val make_the_value : forall n. Z -> itself n
Definition inline make_the_value x := the_value
*)

Fixpoint bitlistFromWord {n} w :=
match w with
| WO => []
| WS b w => b :: bitlistFromWord w
end.

Fixpoint wordFromBitlist l : word (length l) :=
match l with
| [] => WO
| b::t => WS b (wordFromBitlist t)
end.

Local Open Scope nat.
Program Definition fit_bbv_word {n m} (w : word n) : word m :=
match Nat.compare m n with
| Gt => extz w (m - n)
| Eq => w
| Lt => split2 (n - m) m w
end.
Next Obligation.
symmetry in Heq_anonymous.
apply nat_compare_gt in Heq_anonymous.
omega.
Defined.
Next Obligation.

symmetry in Heq_anonymous.
apply nat_compare_eq in Heq_anonymous.
omega.
Defined.
Next Obligation.

symmetry in Heq_anonymous.
apply nat_compare_lt in Heq_anonymous.
omega.
Defined.
Local Close Scope nat.

(*** Bitvectors *)

Class Bitvector (a:Type) : Type := {
  bits_of : a -> list bitU;
  of_bits : list bitU -> option a;
  of_bools : list bool -> a;
  (* The first parameter specifies the desired length of the bitvector *)
  of_int : Z -> Z -> a;
  length : a -> Z;
  unsigned : a -> option Z;
  signed : a -> option Z;
  arith_op_bv : (Z -> Z -> Z) -> bool -> a -> a -> a
}.

Instance bitlist_Bitvector {a : Type} `{BitU a} : (Bitvector (list a)) := {
  bits_of v := List.map to_bitU v;
  of_bits v := Some (List.map of_bitU v);
  of_bools v := List.map of_bitU (List.map bitU_of_bool v);
  of_int len n := List.map of_bitU (bits_of_int len n);
  length := length_list;
  unsigned v := unsigned_of_bits (List.map to_bitU v);
  signed v := signed_of_bits (List.map to_bitU v);
  arith_op_bv op sign l r := List.map of_bitU (arith_op_bits op sign (List.map to_bitU l) (List.map to_bitU r))
}.

Class ReasonableSize (a : Z) : Prop := {
  isPositive : a >= 0
}.

Hint Resolve -> Z.gtb_lt Z.geb_le Z.ltb_lt Z.leb_le : zbool.
Hint Resolve <- Z.ge_le_iff Z.gt_lt_iff : zbool.

Lemma ArithFact_mword (a : Z) (w : mword a) : ArithFact (a >= 0).
constructor.
destruct a.
auto with zarith.
auto using Z.le_ge, Zle_0_pos.
destruct w.
Qed.
Ltac unwrap_ArithFacts :=
  repeat match goal with H:(ArithFact _) |- _ => apply use_ArithFact in H end.
Ltac unbool_comparisons :=
  repeat match goal with
  | H:context [Z.geb _ _] |- _ => rewrite Z.geb_leb in H
  | H:context [Z.gtb _ _] |- _ => rewrite Z.gtb_ltb in H
  | H:context [Z.leb _ _ = true] |- _ => rewrite Z.leb_le in H
  | H:context [Z.ltb _ _ = true] |- _ => rewrite Z.ltb_lt in H
  | H:context [Z.eqb _ _ = true] |- _ => rewrite Z.eqb_eq in H
  | H:context [Z.leb _ _ = false] |- _ => rewrite Z.leb_gt in H
  | H:context [Z.ltb _ _ = false] |- _ => rewrite Z.ltb_ge in H
  | H:context [Z.eqb _ _ = false] |- _ => rewrite Z.eqb_neq in H
  | H:context [orb _ _ = true] |- _ => rewrite Bool.orb_true_iff in H
  | H:context [generic_eq _ _ = true] |- _ => apply generic_eq_true in H
  | H:context [generic_eq _ _ = false] |- _ => apply generic_eq_false in H
  | H:context [generic_neq _ _ = true] |- _ => apply generic_neq_true in H
  | H:context [generic_neq _ _ = false] |- _ => apply generic_neq_false in H
  end.
(* Split up dependent pairs to get at proofs of properties *)
Ltac extract_properties :=
  repeat match goal with H := (projT1 ?X) |- _ =>
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    destruct X as [x Hx] in *;
    change (projT1 (existT _ x Hx)) with x in *; unfold H in * end;
  repeat match goal with |- context [projT1 ?X] =>
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    destruct X as [x Hx] in *;
    change (projT1 (existT _ x Hx)) with x in * end.
(* TODO: hyps, too? *)
Ltac reduce_list_lengths :=
  repeat match goal with |- context [length_list ?X] => 
    let r := (eval cbn in (length_list X)) in
    change (length_list X) with r
  end.
(* TODO: can we restrict this to concrete terms? *)
Ltac reduce_pow :=
  repeat match goal with H:context [Z.pow ?X ?Y] |- _ => 
    let r := (eval cbn in (Z.pow X Y)) in
    change (Z.pow X Y) with r in H
  end;
  repeat match goal with |- context [Z.pow ?X ?Y] => 
    let r := (eval cbn in (Z.pow X Y)) in
    change (Z.pow X Y) with r
  end.
Ltac solve_arithfact :=
 extract_properties;
 repeat match goal with w:mword ?n |- _ => apply ArithFact_mword in w end;
 unwrap_ArithFacts;
 autounfold with sail in * |- *; (* You can add Hint Unfold ... : sail to let omega see through fns *)
 unbool_comparisons;
 reduce_list_lengths;
 reduce_pow;
 solve [apply ArithFact_mword; assumption
       | constructor; omega with Z
         (* The datatypes hints give us some list handling, esp In *)
       | constructor; auto with datatypes zbool zarith sail].
Hint Extern 0 (ArithFact _) => solve_arithfact : typeclass_instances.

Hint Unfold length_mword : sail.

Lemma ReasonableSize_witness (a : Z) (w : mword a) : ReasonableSize a.
constructor.
destruct a.
auto with zarith.
auto using Z.le_ge, Zle_0_pos.
destruct w.
Qed.

Hint Extern 0 (ReasonableSize ?A) => (unwrap_ArithFacts; solve [apply ReasonableSize_witness; assumption | constructor; omega]) : typeclass_instances.

Instance mword_Bitvector {a : Z} `{ArithFact (a >= 0)} : (Bitvector (mword a)) := {
  bits_of v := List.map bitU_of_bool (bitlistFromWord (get_word v));
  of_bits v := option_map (fun bl => to_word isPositive (fit_bbv_word (wordFromBitlist bl))) (just_list (List.map bool_of_bitU v));
  of_bools v := to_word isPositive (fit_bbv_word (wordFromBitlist v));
  of_int len z := mword_of_int z; (* cheat a little *)
  length v := a;
  unsigned v := Some (Z.of_N (wordToN (get_word v)));
  signed v := Some (wordToZ (get_word v));
  arith_op_bv op sign l r := mword_of_int (op (int_of_mword sign l) (int_of_mword sign r))
}.

Section Bitvector_defs.
Context {a b} `{Bitvector a} `{Bitvector b}.

Definition opt_def {a} (def:a) (v:option a) :=
match v with
| Some x => x
| None => def
end.

(* The Lem version is partial, but lets go with BU here to avoid constraints for now *)
Definition access_bv_inc (v : a) n := opt_def BU (access_list_opt_inc (bits_of v) n).
Definition access_bv_dec (v : a) n := opt_def BU (access_list_opt_dec (bits_of v) n).

Definition update_bv_inc (v : a) n b := update_list true  (bits_of v) n b.
Definition update_bv_dec (v : a) n b := update_list false (bits_of v) n b.

Definition subrange_bv_inc (v : a) i j := subrange_list true  (bits_of v) i j.
Definition subrange_bv_dec (v : a) i j := subrange_list true  (bits_of v) i j.

Definition update_subrange_bv_inc (v : a) i j (v' : b) := update_subrange_list true  (bits_of v) i j (bits_of v').
Definition update_subrange_bv_dec (v : a) i j (v' : b) := update_subrange_list false (bits_of v) i j (bits_of v').

(*val extz_bv : forall a b. Bitvector a, Bitvector b => Z -> a -> b*)
Definition extz_bv n (v : a) : option b := of_bits (extz_bits n (bits_of v)).

(*val exts_bv : forall a b. Bitvector a, Bitvector b => Z -> a -> b*)
Definition exts_bv n (v : a) : option b := of_bits (exts_bits n (bits_of v)).

(*val string_of_bv : forall a. Bitvector a => a -> string
Definition string_of_bv v := show_bitlist (bits_of v)
*)
End Bitvector_defs.

(*** Bytes and addresses *)

Definition memory_byte := list bitU.

(*val byte_chunks : forall a. list a -> option (list (list a))*)
Fixpoint byte_chunks {a} (bs : list a) := match bs with
  | [] => Some []
  | a::b::c::d::e::f::g::h::rest =>
     match byte_chunks rest with
     | None => None
     | Some rest => Some ([a;b;c;d;e;f;g;h] :: rest)
     end
  | _ => None
end.
(*declare {isabelle} termination_argument byte_chunks = automatic*)

Section BytesBits.
Context {a} `{Bitvector a}.

(*val bytes_of_bits : forall a. Bitvector a => a -> option (list memory_byte)*)
Definition bytes_of_bits (bs : a) := byte_chunks (bits_of bs).

(*val bits_of_bytes : forall a. Bitvector a => list memory_byte -> a*)
Definition bits_of_bytes (bs : list memory_byte) : list bitU := List.concat (List.map bits_of bs).

Definition mem_bytes_of_bits (bs : a) := option_map (@rev (list bitU)) (bytes_of_bits bs).
Definition bits_of_mem_bytes (bs : list memory_byte) := bits_of_bytes (List.rev bs).

End BytesBits.

(*val bitv_of_byte_lifteds : list Sail_impl_base.byte_lifted -> list bitU
Definition bitv_of_byte_lifteds v :=
  foldl (fun x (Byte_lifted y) => x ++ (List.map bitU_of_bit_lifted y)) [] v

val bitv_of_bytes : list Sail_impl_base.byte -> list bitU
Definition bitv_of_bytes v :=
  foldl (fun x (Byte y) => x ++ (List.map bitU_of_bit y)) [] v

val byte_lifteds_of_bitv : list bitU -> list byte_lifted
Definition byte_lifteds_of_bitv bits :=
  let bits := List.map bit_lifted_of_bitU bits in
  byte_lifteds_of_bit_lifteds bits

val bytes_of_bitv : list bitU -> list byte
Definition bytes_of_bitv bits :=
  let bits := List.map bit_of_bitU bits in
  bytes_of_bits bits

val bit_lifteds_of_bitUs : list bitU -> list bit_lifted
Definition bit_lifteds_of_bitUs bits := List.map bit_lifted_of_bitU bits

val bit_lifteds_of_bitv : list bitU -> list bit_lifted
Definition bit_lifteds_of_bitv v := bit_lifteds_of_bitUs v


val address_lifted_of_bitv : list bitU -> address_lifted
Definition address_lifted_of_bitv v :=
  let byte_lifteds := byte_lifteds_of_bitv v in
  let maybe_address_integer :=
    match (maybe_all (List.map byte_of_byte_lifted byte_lifteds)) with
    | Some bs => Some (integer_of_byte_list bs)
    | _ => None
    end in
  Address_lifted byte_lifteds maybe_address_integer

val bitv_of_address_lifted : address_lifted -> list bitU
Definition bitv_of_address_lifted (Address_lifted bs _) := bitv_of_byte_lifteds bs

val address_of_bitv : list bitU -> address
Definition address_of_bitv v :=
  let bytes := bytes_of_bitv v in
  address_of_byte_list bytes*)

Fixpoint reverse_endianness_list (bits : list bitU) :=
  match bits with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: t =>
    reverse_endianness_list t ++ firstn 8 bits
  | _ => bits
  end.

(*** Registers *)

Definition register_field := string.
Definition register_field_index : Type := string * (Z * Z). (* name, start and end *)

Inductive register :=
  | Register : string * (* name *)
               Z * (* length *)
               Z * (* start index *)
               bool * (* is increasing *)
               list register_field_index
               -> register
  | UndefinedRegister : Z -> register (* length *)
  | RegisterPair : register * register -> register.

Record register_ref regstate regval a :=
   { name : string;
     (*is_inc : bool;*)
     read_from : regstate -> a;
     write_to : a -> regstate -> regstate;
     of_regval : regval -> option a;
     regval_of : a -> regval }.
Notation "{[ r 'with' 'name' := e ]}" := ({| name := e; read_from := read_from r; write_to := write_to r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'read_from' := e ]}" := ({| read_from := e; name := name r; write_to := write_to r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'write_to' := e ]}" := ({| write_to := e; name := name r; read_from := read_from r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'of_regval' := e ]}" := ({| of_regval := e; name := name r; read_from := read_from r; write_to := write_to r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'regval_of' := e ]}" := ({| regval_of := e; name := name r; read_from := read_from r; write_to := write_to r; of_regval := of_regval r |}).
Arguments name [_ _ _].
Arguments read_from [_ _ _].
Arguments write_to [_ _ _].
Arguments of_regval [_ _ _].
Arguments regval_of [_ _ _].

(* Register accessors: pair of functions for reading and writing register values *)
Definition register_accessors regstate regval : Type :=
  ((string -> regstate -> option regval) *
   (string -> regval -> regstate -> option regstate)).

Record field_ref regtype a :=
   { field_name : string;
     field_start : Z;
     field_is_inc : bool;
     get_field : regtype -> a;
     set_field : regtype -> a -> regtype }.
Arguments field_name [_ _].
Arguments field_start [_ _].
Arguments field_is_inc [_ _].
Arguments get_field [_ _].
Arguments set_field [_ _].

(*
(*let name_of_reg := function
  | Register name _ _ _ _ => name
  | UndefinedRegister _ => failwith "name_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "name_of_reg RegisterPair"
end

Definition size_of_reg := function
  | Register _ size _ _ _ => size
  | UndefinedRegister size => size
  | RegisterPair _ _ => failwith "size_of_reg RegisterPair"
end

Definition start_of_reg := function
  | Register _ _ start _ _ => start
  | UndefinedRegister _ => failwith "start_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "start_of_reg RegisterPair"
end

Definition is_inc_of_reg := function
  | Register _ _ _ is_inc _ => is_inc
  | UndefinedRegister _ => failwith "is_inc_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "in_inc_of_reg RegisterPair"
end

Definition dir_of_reg := function
  | Register _ _ _ is_inc _ => dir_of_bool is_inc
  | UndefinedRegister _ => failwith "dir_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "dir_of_reg RegisterPair"
end

Definition size_of_reg_nat reg := Z.to_nat (size_of_reg reg)
Definition start_of_reg_nat reg := Z.to_nat (start_of_reg reg)

val register_field_indices_aux : register -> register_field -> option (Z * Z)
Fixpoint register_field_indices_aux register rfield :=
  match register with
  | Register _ _ _ _ rfields => List.lookup rfield rfields
  | RegisterPair r1 r2 =>
      let m_indices := register_field_indices_aux r1 rfield in
      if isSome m_indices then m_indices else register_field_indices_aux r2 rfield
  | UndefinedRegister _ => None
  end

val register_field_indices : register -> register_field -> Z * Z
Definition register_field_indices register rfield :=
  match register_field_indices_aux register rfield with
  | Some indices => indices
  | None => failwith "Invalid register/register-field combination"
  end

Definition register_field_indices_nat reg regfield=
  let (i,j) := register_field_indices reg regfield in
  (Z.to_nat i,Z.to_nat j)*)

(*let rec external_reg_value reg_name v :=
  let (internal_start, external_start, direction) :=
    match reg_name with
     | Reg _ start size dir =>
        (start, (if dir = D_increasing then start else (start - (size +1))), dir)
     | Reg_slice _ reg_start dir (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     | Reg_field _ reg_start dir _ (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     | Reg_f_slice _ reg_start dir _ _ (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     end in
  let bits := bit_lifteds_of_bitv v in
  <| rv_bits           := bits;
     rv_dir            := direction;
     rv_start          := external_start;
     rv_start_internal := internal_start |>

val internal_reg_value : register_value -> list bitU
Definition internal_reg_value v :=
  List.map bitU_of_bit_lifted v.rv_bits
         (*(Z.of_nat v.rv_start_internal)
         (v.rv_dir = D_increasing)*)


Definition external_slice (d:direction) (start:nat) ((i,j):(nat*nat)) :=
  match d with
  (*This is the case the thread/concurrecny model expects, so no change needed*)
  | D_increasing => (i,j)
  | D_decreasing => let slice_i = start - i in
                    let slice_j = (i - j) + slice_i in
                    (slice_i,slice_j)
  end *)

(* TODO
Definition external_reg_whole r :=
  Reg (r.name) (Z.to_nat r.start) (Z.to_nat r.size) (dir_of_bool r.is_inc)

Definition external_reg_slice r (i,j) :=
  let start := Z.to_nat r.start in
  let dir := dir_of_bool r.is_inc in
  Reg_slice (r.name) start dir (external_slice dir start (i,j))

Definition external_reg_field_whole reg rfield :=
  let (m,n) := register_field_indices_nat reg rfield in
  let start := start_of_reg_nat reg in
  let dir := dir_of_reg reg in
  Reg_field (name_of_reg reg) start dir rfield (external_slice dir start (m,n))

Definition external_reg_field_slice reg rfield (i,j) :=
  let (m,n) := register_field_indices_nat reg rfield in
  let start := start_of_reg_nat reg in
  let dir := dir_of_reg reg in
  Reg_f_slice (name_of_reg reg) start dir rfield
              (external_slice dir start (m,n))
              (external_slice dir start (i,j))*)

(*val external_mem_value : list bitU -> memory_value
Definition external_mem_value v :=
  byte_lifteds_of_bitv v $> List.reverse

val internal_mem_value : memory_value -> list bitU
Definition internal_mem_value bytes :=
  List.reverse bytes $> bitv_of_byte_lifteds*)


val foreach : forall a vars.
  (list a) -> vars -> (a -> vars -> vars) -> vars*)
Fixpoint foreach {a Vars} (l : list a) (vars : Vars) (body : a -> Vars -> Vars) : Vars :=
match l with
| [] => vars
| (x :: xs) => foreach xs (body x vars) body
end.

(*declare {isabelle} termination_argument foreach = automatic

val index_list : Z -> Z -> Z -> list Z*)
Fixpoint index_list' from step n :=
  match n with
  | O => []
  | S n => from :: index_list' (from + step) step n
  end.

Definition index_list from to step :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    index_list' from step (S (Z.abs_nat (from - to)))
  else [].

(*val while : forall vars. vars -> (vars -> bool) -> (vars -> vars) -> vars
Fixpoint while vars cond body :=
  if cond vars then while (body vars) cond body else vars

val until : forall vars. vars -> (vars -> bool) -> (vars -> vars) -> vars
Fixpoint until vars cond body :=
  let vars := body vars in
  if cond vars then vars else until (body vars) cond body


Definition assert' b msg_opt :=
  let msg := match msg_opt with
  | Some msg => msg
  | None  => "unspecified error"
  end in
  if b then () else failwith msg

(* convert numbers unsafely to naturals *)

class (ToNatural a) val toNatural : a -> natural end
(* eta-expanded for Isabelle output, otherwise it breaks *)
instance (ToNatural Z) let toNatural := (fun n => naturalFromInteger n) end
instance (ToNatural int)     let toNatural := (fun n => naturalFromInt n)     end
instance (ToNatural nat)     let toNatural := (fun n => naturalFromNat n)     end
instance (ToNatural natural) let toNatural := (fun n => n)                    end

Definition toNaturalFiveTup (n1,n2,n3,n4,n5) :=
  (toNatural n1,
   toNatural n2,
   toNatural n3,
   toNatural n4,
   toNatural n5)

(* Let the following types be generated by Sail per spec, using either bitlists
   or machine words as bitvector representation *)
(*type regfp :=
  | RFull of (string)
  | RSlice of (string * Z * Z)
  | RSliceBit of (string * Z)
  | RField of (string * string)

type niafp :=
  | NIAFP_successor
  | NIAFP_concrete_address of vector bitU
  | NIAFP_indirect_address

(* only for MIPS *)
type diafp :=
  | DIAFP_none
  | DIAFP_concrete of vector bitU
  | DIAFP_reg of regfp

Definition regfp_to_reg (reg_info : string -> option string -> (nat * nat * direction * (nat * nat))) := function
  | RFull name =>
     let (start,length,direction,_) := reg_info name None in
     Reg name start length direction
  | RSlice (name,i,j) =>
     let i = Z.to_nat i in
     let j = Z.to_nat j in
     let (start,length,direction,_) = reg_info name None in
     let slice = external_slice direction start (i,j) in
     Reg_slice name start direction slice
  | RSliceBit (name,i) =>
     let i = Z.to_nat i in
     let (start,length,direction,_) = reg_info name None in
     let slice = external_slice direction start (i,i) in
     Reg_slice name start direction slice
  | RField (name,field_name) =>
     let (start,length,direction,span) = reg_info name (Some field_name) in
     let slice = external_slice direction start span in
     Reg_field name start direction field_name slice
end

Definition niafp_to_nia reginfo = function
  | NIAFP_successor => NIA_successor
  | NIAFP_concrete_address v => NIA_concrete_address (address_of_bitv v)
  | NIAFP_indirect_address => NIA_indirect_address
end

Definition diafp_to_dia reginfo = function
  | DIAFP_none => DIA_none
  | DIAFP_concrete v => DIA_concrete_address (address_of_bitv v)
  | DIAFP_reg r => DIA_register (regfp_to_reg reginfo r)
end
*)
*)

(* Arithmetic functions which return proofs that match the expected Sail
   types in smt.sail. *)

Definition div_with_eq n m : {o : Z & ArithFact (o = Z.quot n m)} := build_ex (Z.quot n m).
Definition mod_with_eq n m : {o : Z & ArithFact (o = Z.rem n m)} := build_ex (Z.rem n m).
Definition abs_with_eq n   : {o : Z & ArithFact (o = Z.abs n)} := build_ex (Z.abs n).

(* Similarly, for ranges (currently in MIPS) *)

Definition add_range {n m o p} (l : {l & ArithFact (n <= l <= m)}) (r : {r & ArithFact (o <= r <= p)})
  : {x & ArithFact (n+o <= x <= m+p)} :=
  build_ex ((projT1 l) + (projT1 r)).
Definition sub_range {n m o p} (l : {l & ArithFact (n <= l <= m)}) (r : {r & ArithFact (o <= r <= p)})
  : {x & ArithFact (n-p <= x <= m-o)} :=
  build_ex ((projT1 l) - (projT1 r)).
Definition negate_range {n m} (l : {l : Z & ArithFact (n <= l <= m)})
  : {x : Z & ArithFact ((- m) <= x <= (- n))} :=
  build_ex (- (projT1 l)).

Definition min_atom (a : Z) (b : Z) : {c : Z & ArithFact (c = a \/ c = b /\ c <= a /\ c <= b)} :=
  build_ex (Z.min a b).
Definition max_atom (a : Z) (b : Z) : {c : Z & ArithFact (c = a \/ c = b /\ c >= a /\ c >= b)} :=
  build_ex (Z.max a b).

