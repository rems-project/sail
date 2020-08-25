(* Version of sail_values.lem that uses Lems machine words library *)

(*Require Import Sail_impl_base*)
Require Export ZArith.
Require Import Ascii.
Require Export String.
Require Import bbv.Word.
Require Export bbv.HexNotationWord.
Require Export List.
Require Export Sumbool.
Require Export DecidableClass.
Require Import Eqdep_dec.
Require Export Zeuclid.
Require Import Lia.
Import ListNotations.

Local Open Scope Z.
Local Open Scope bool.

Module Z_eq_dec.
Definition U := Z.
Definition eq_dec := Z.eq_dec.
End Z_eq_dec.
Module ZEqdep := DecidableEqDep (Z_eq_dec).


(* Constraint solving basics.  A HintDb which unfolding hints and lemmata
   can be added to, and a typeclass to wrap constraint arguments in to
   trigger automatic solving. *)
Create HintDb sail.
(* Facts translated from Sail's type system are wrapped in ArithFactP or
   ArithFact so that the solver can be invoked automatically by Coq's
   typeclass mechanism.  Most properties are boolean, which enjoys proof
   irrelevance by UIP. *)
Class ArithFactP (P : Prop) := { fact : P }.
Class ArithFact (P : bool) := ArithFactClass : ArithFactP (P = true).
Lemma use_ArithFact {P} `(ArithFact P) : P = true.
unfold ArithFact in *.
apply fact.
Defined.

Lemma ArithFact_irrelevant (P : bool) (p q : ArithFact P) : p = q.
destruct p,q.
f_equal.
apply Eqdep_dec.UIP_dec.
apply Bool.bool_dec.
Qed.

Ltac replace_ArithFact_proof :=
  match goal with |- context[?x] =>
    match tt with
    | _ => is_var x; fail 1
    | _ =>
      match type of x with ArithFact ?P =>
        let pf := fresh "pf" in
        generalize x as pf; intro pf;
        repeat multimatch goal with |- context[?y] =>
          match type of y with ArithFact P =>
            match y with
            | pf => idtac
            | _ => rewrite <- (ArithFact_irrelevant P pf y)
            end
          end
        end
      end
    end
  end.

Ltac generalize_ArithFact_proof_in H :=
  match type of H with context f [?x] =>
    match type of x with ArithFactP (?P = true) =>
      let pf := fresh "pf" in
      cut (forall (pf : ArithFact P), ltac:(let t := context f[pf] in exact t));
      [ clear H; intro H
      | intro pf; rewrite <- (ArithFact_irrelevant P x pf); apply H ]
    | ArithFact ?P =>
      let pf := fresh "pf" in
      cut (forall (pf : ArithFact P), ltac:(let t := context f[pf] in exact t));
      [ clear H; intro H
      | intro pf; rewrite <- (ArithFact_irrelevant P x pf); apply H ]
    end
  end.

(* Allow setoid rewriting through ArithFact *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Section Morphism.
Local Obligation Tactic := try solve [simpl_relation | firstorder auto].
Global Program Instance ArithFactP_iff_morphism :
  Proper (iff ==> iff) ArithFactP.
End Morphism.

Definition build_ex {T:Type} (n:T) {P:T -> Prop} `{H:ArithFactP (P n)} : {x : T & ArithFactP (P x)} :=
  existT _ n H.

Definition build_ex2 {T:Type} {T':T -> Type} (n:T) (m:T' n) {P:T -> Prop} `{H:ArithFactP (P n)} : {x : T & T' x & ArithFactP (P x)} :=
  existT2 _ _ n m H.

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
  forall (x y : T), Decidable (eq x y).
refine (fun x y => {|
  Decidable_witness := proj1_sig (bool_of_sumbool (eqdec x y))
|}).
destruct (eqdec x y); simpl; split; congruence.
Defined.

Instance Decidable_eq_unit : forall (x y : unit), Decidable (x = y).
refine (fun x y => {| Decidable_witness := true |}).
destruct x, y; split; auto.
Defined.

Instance Decidable_eq_string : forall (x y : string), Decidable (x = y) :=
  Decidable_eq_from_dec String.string_dec.

Instance Decidable_eq_pair {A B : Type} `(DA : forall x y : A, Decidable (x = y), DB : forall x y : B, Decidable (x = y)) : forall x y : A*B, Decidable (x = y).
refine (fun x y =>
{| Decidable_witness := andb (@Decidable_witness _ (DA (fst x) (fst y)))
     (@Decidable_witness _ (DB (snd x) (snd y))) |}).
destruct x as [x1 x2].
destruct y as [y1 y2].
simpl.
destruct (DA x1 y1) as [b1 H1];
destruct (DB x2 y2) as [b2 H2];
simpl.
split.
* intro H.
  apply Bool.andb_true_iff in H.
  destruct H as [H1b H2b].
  apply H1 in H1b.
  apply H2 in H2b.
  congruence.
* intro. inversion H.
  subst.
  apply Bool.andb_true_iff.
  tauto.
Qed.

Definition generic_dec {T:Type} (x y:T) `{Decidable (x = y)} : {x = y} + {x <> y}.
refine ((if Decidable_witness as b return (b = true <-> x = y -> _) then fun H' => _ else fun H' => _) Decidable_spec).
* left. tauto.
* right. intuition.
Defined.

Instance Decidable_eq_list {A : Type} `(D : forall x y : A, Decidable (x = y)) : forall (x y : list A), Decidable (x = y) :=
  Decidable_eq_from_dec (list_eq_dec (fun x y => generic_dec x y)).

(* Used by generated code that builds Decidable equality instances for records. *)
Ltac cmp_record_field x y :=
  let H := fresh "H" in
  case (generic_dec x y);
  intro H; [ |
    refine (Build_Decidable _ false _);
    split; [congruence | intros Z; destruct H; injection Z; auto]
  ].


Notation "x <=? y <=? z" := ((x <=? y) && (y <=? z)) (at level 70, y at next level) : Z_scope.
Notation "x <=? y <? z" := ((x <=? y) && (y <? z)) (at level 70, y at next level) : Z_scope.
Notation "x <? y <? z" := ((x <? y) && (y <? z)) (at level 70, y at next level) : Z_scope.
Notation "x <? y <=? z" := ((x <? y) && (y <=? z)) (at level 70, y at next level) : Z_scope.

(* Project away range constraints in comparisons *)
Definition ltb_range_l {lo hi} (l : {x & ArithFact (lo <=? x <=? hi)}) r := Z.ltb (projT1 l) r.
Definition leb_range_l {lo hi} (l : {x & ArithFact (lo <=? x <=? hi)}) r := Z.leb (projT1 l) r.
Definition gtb_range_l {lo hi} (l : {x & ArithFact (lo <=? x <=? hi)}) r := Z.gtb (projT1 l) r.
Definition geb_range_l {lo hi} (l : {x & ArithFact (lo <=? x <=? hi)}) r := Z.geb (projT1 l) r.
Definition ltb_range_r {lo hi} l (r : {x & ArithFact (lo <=? x <=? hi)}) := Z.ltb l (projT1 r).
Definition leb_range_r {lo hi} l (r : {x & ArithFact (lo <=? x <=? hi)}) := Z.leb l (projT1 r).
Definition gtb_range_r {lo hi} l (r : {x & ArithFact (lo <=? x <=? hi)}) := Z.gtb l (projT1 r).
Definition geb_range_r {lo hi} l (r : {x & ArithFact (lo <=? x <=? hi)}) := Z.geb l (projT1 r).

Definition ii := Z.
Definition nn := nat.

(*val pow : Z -> Z -> Z*)
Definition pow m n := m ^ n.

Program Definition pow2 n : {z : Z & ArithFact (2 ^ n <=? z <=? 2 ^ n)} := existT _ (pow 2 n) _.
Next Obligation.
constructor.
unfold pow.
auto using Z.leb_refl with bool.
Qed.

Lemma ZEuclid_div_pos : forall x y, 0 < y -> 0 <= x -> 0 <= ZEuclid.div x y.
intros.
unfold ZEuclid.div.
change 0 with (0 * 0).
apply Zmult_le_compat.
3,4: auto with zarith.
* apply Z.sgn_nonneg. auto with zarith.
* apply Z_div_pos; auto. apply Z.lt_gt. apply Z.abs_pos. auto with zarith.
Qed.

Lemma ZEuclid_pos_div : forall x y, 0 < y -> 0 <= ZEuclid.div x y -> 0 <= x.
intros x y GT.
  specialize (ZEuclid.div_mod x y);
  specialize (ZEuclid.mod_always_pos x y);
  generalize (ZEuclid.modulo x y);
  generalize (ZEuclid.div x y);
  intros.
nia.
Qed.

Lemma ZEuclid_div_ge : forall x y, y > 0 -> x >= 0 -> x - ZEuclid.div x y >= 0.
intros.
unfold ZEuclid.div.
rewrite Z.sgn_pos. 2: solve [ auto with zarith ].
rewrite Z.mul_1_l.
apply Z.le_ge.
apply Zle_minus_le_0.
apply Z.div_le_upper_bound.
* apply Z.abs_pos. auto with zarith.
* rewrite Z.mul_comm.
  nia.
Qed.

Lemma ZEuclid_div_mod0 : forall x y, y <> 0 ->
  ZEuclid.modulo x y = 0 ->
  y * ZEuclid.div x y = x.
intros x y H1 H2.
rewrite Zplus_0_r_reverse at 1.
rewrite <- H2.
symmetry.
apply ZEuclid.div_mod.
assumption.
Qed.

Hint Resolve ZEuclid_div_pos ZEuclid_pos_div ZEuclid_div_ge ZEuclid_div_mod0 : sail.

Lemma Z_geb_ge n m : (n >=? m) = true <-> n >= m.
rewrite Z.geb_leb.
split.
* intro. apply Z.le_ge, Z.leb_le. assumption.
* intro. apply Z.ge_le in H. apply Z.leb_le. assumption.
Qed.


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

Definition print_endline (_ : string) : unit := tt.
Definition prerr_endline (_ : string) : unit := tt.
Definition prerr (_ : string) : unit := tt.
Definition print_int (_ : string) (_ : Z) : unit := tt.
Definition prerr_int (_ : string) (_ : Z) : unit := tt.
Definition putchar (_ : Z) : unit := tt.

Definition shl_int := Z.shiftl.
Definition shr_int := Z.shiftr.

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
Lemma repeat'_length {a} {xs : list a} {n : nat} : List.length (repeat' xs n) = (n * List.length xs)%nat.
induction n.
* reflexivity.
* simpl.
  rewrite app_length.
  auto with arith.
Qed.
Definition repeat {a} (xs : list a) (n : Z) :=
  if n <=? 0 then []
  else repeat' xs (Z.to_nat n).
Lemma repeat_length {a} {xs : list a} {n : Z} (H : n >= 0) : length_list (repeat xs n) = n * length_list xs.
unfold length_list, repeat.
destruct n.
+ reflexivity. 
+ simpl (List.length _).
  rewrite repeat'_length.
  rewrite Nat2Z.inj_mul.
  rewrite positive_nat_Z.
  reflexivity.  
+ exfalso.
  auto with zarith.
Qed.

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

Lemma just_list_length {A} : forall (l : list (option A)) (l' : list A),
  Some l' = just_list l -> List.length l = List.length l'.
induction l.
* intros.
  simpl in H.
  inversion H.
  reflexivity.
* intros.
  destruct a; simplify_eq H.
  simpl in *.
  destruct (just_list l); simplify_eq H.
  intros.
  subst.
  simpl.
  f_equal.
  apply IHl.
  reflexivity.
Qed.

Lemma just_list_length_Z {A} : forall (l : list (option A)) l', Some l' = just_list l -> length_list l = length_list l'.
unfold length_list.
intros.
f_equal.
auto using just_list_length.
Qed.

Fixpoint member_Z_list (x : Z) (l : list Z) : bool :=
match l with
| [] => false
| h::t => if x =? h then true else member_Z_list x t
end.

Lemma member_Z_list_In {x l} : member_Z_list x l = true <-> In x l.
induction l.
* simpl. split. congruence. tauto.
* simpl. destruct (x =? a) eqn:H.
  + rewrite Z.eqb_eq in H. subst. tauto.
  + rewrite Z.eqb_neq in H. split.
    - intro Heq. right. apply IHl. assumption.
    - intros [bad | good]. congruence. apply IHl. assumption.
Qed.

(*** Bits *)
Inductive bitU := B0 | B1 | BU.

Scheme Equality for bitU.
Definition eq_bit := bitU_beq.
Instance Decidable_eq_bit : forall (x y : bitU), Decidable (x = y) :=
  Decidable_eq_from_dec bitU_eq_dec.

Definition showBitU b :=
match b with
  | B0 => "O"
  | B1 => "I"
  | BU => "U"
end%string.

Definition bitU_char b :=
match b with
| B0 => "0"
| B1 => "1"
| BU => "?"
end%char.

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
(*  | (x,y) => bitU_of_bool (op (bool_of_bitU x) (bool_of_bitU y))*)
  | (B0,B0) => bitU_of_bool (op false false)
  | (B0,B1) => bitU_of_bool (op false  true)
  | (B1,B0) => bitU_of_bool (op  true false)
  | (B1,B1) => bitU_of_bool (op  true  true)
  end.

(*val and_bit : bitU -> bitU -> bitU*)
Definition and_bit := binop_bit andb.

(*val or_bit : bitU -> bitU -> bitU*)
Definition or_bit := binop_bit orb.

(*val xor_bit : bitU -> bitU -> bitU*)
Definition xor_bit := binop_bit xorb.

(*val (&.) : bitU -> bitU -> bitU
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

(* Ported from Lem, bad for large n.
Definition bools_of_int len n :=
  let bs_abs := bools_of_nat len (Z.abs_nat n) in
  if n >=? 0 then bs_abs
  else add_one_bool_ignore_overflow (List.map negb bs_abs).
*)
Fixpoint bitlistFromWord_rev {n} w :=
match w with
| WO => []
| WS b w => b :: bitlistFromWord_rev w
end.
Definition bitlistFromWord {n} w :=
  List.rev (@bitlistFromWord_rev n w).

Definition bools_of_int len n :=
  let w := Word.ZToWord (Z.to_nat len) n in
  bitlistFromWord w.

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


Definition char_of_nibble x :=
  match x with
  | (B0, B0, B0, B0) => Some "0"%char
  | (B0, B0, B0, B1) => Some "1"%char
  | (B0, B0, B1, B0) => Some "2"%char
  | (B0, B0, B1, B1) => Some "3"%char
  | (B0, B1, B0, B0) => Some "4"%char
  | (B0, B1, B0, B1) => Some "5"%char
  | (B0, B1, B1, B0) => Some "6"%char
  | (B0, B1, B1, B1) => Some "7"%char
  | (B1, B0, B0, B0) => Some "8"%char
  | (B1, B0, B0, B1) => Some "9"%char
  | (B1, B0, B1, B0) => Some "A"%char
  | (B1, B0, B1, B1) => Some "B"%char
  | (B1, B1, B0, B0) => Some "C"%char
  | (B1, B1, B0, B1) => Some "D"%char
  | (B1, B1, B1, B0) => Some "E"%char
  | (B1, B1, B1, B1) => Some "F"%char
  | _ => None
  end.

Fixpoint hexstring_of_bits bs := match bs with
  | b1 :: b2 :: b3 :: b4 :: bs =>
     let n := char_of_nibble (b1, b2, b3, b4) in
     let s := hexstring_of_bits bs in
     match (n, s) with
     | (Some n, Some s) => Some (String n s)
     | _ => None
     end
  | [] => Some EmptyString
  | _ => None
  end%string.

Fixpoint binstring_of_bits bs := match bs with
  | b :: bs => String (bitU_char b) (binstring_of_bits bs)
  | [] => EmptyString
  end.

Definition show_bitlist bs :=
  match hexstring_of_bits bs with
  | Some s => String "0" (String "x" s)
  | None => String "0" (String "b" (binstring_of_bits bs))
  end.

(*** List operations *)
(*
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
simpl in H. lia.
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

Close Scope nat.

(*val access_list_inc : forall a. list a -> Z -> a*)
Definition access_list_inc {A} (xs : list A) n `{ArithFact (0 <=? n)} `{ArithFact (n <? length_list xs)} : A.
refine (nth_in_range (Z.to_nat n) xs (nth_Z_nat _ _)).
* apply Z.leb_le.
  auto using use_ArithFact.
* apply Z.ltb_lt.
  auto using use_ArithFact.
Defined.

(*val access_list_dec : forall a. list a -> Z -> a*)
Definition access_list_dec {A} (xs : list A) n `{H1:ArithFact (0 <=? n)} `{H2:ArithFact (n <? length_list xs)} : A.
refine (
  let top := (length_list xs) - 1 in
  @access_list_inc A xs (top - n) _ _).
abstract (constructor; apply use_ArithFact, Z.leb_le in H1; apply use_ArithFact, Z.ltb_lt in H2; apply Z.leb_le; lia).
abstract (constructor; apply use_ArithFact, Z.leb_le in H1; apply use_ArithFact, Z.ltb_lt in H2; apply Z.ltb_lt; lia).
Defined.

(*val access_list : forall a. bool -> list a -> Z -> a*)
Definition access_list {A} (is_inc : bool) (xs : list A) n `{ArithFact (0 <=? n)} `{ArithFact (n <? length_list xs)} :=
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
end*)

(*** Machine words *)

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

Program Definition to_word {n} : n >=? 0 = true -> word (Z.to_nat n) -> mword n :=
  match n with
  | Zneg _ => fun H _ => _
  | Z0 => fun _ w => w
  | Zpos _ => fun _ w => w
  end.

Definition word_to_mword {n} (w : word (Z.to_nat n)) `{H:ArithFact (n >=? 0)} : mword n :=
  to_word (use_ArithFact H) w.

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
| S n => fun (w : word (S n)) i => wlsb (wrshift' w i)
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
  let bit : word (S n) := wlshift' (natToWord _ 1) i in
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
Definition int_of_mword {a} `{ArithFact (a >=? 0)} (sign : bool) (w : mword a) :=
  if sign then wordToZ (get_word w) else Z.of_N (wordToN (get_word w)).


(*val mword_of_int : forall a. Size a => Z -> Z -> mword a
Definition mword_of_int len n :=
  let w := wordFromInteger n in
  if (length_mword w = len) then w else failwith "unexpected word length"
*)
Program Definition mword_of_int {len} `{H:ArithFact (len >=? 0)} n : mword len :=
match len with
| Zneg _ => _
| Z0 => ZToWord 0 n
| Zpos p => ZToWord (Pos.to_nat p) n
end.
Next Obligation.
destruct H as [H].
unfold Z.geb, Z.compare in H.
discriminate.
Defined.

(*
(* Translating between a type level number (itself n) and an integer *)

Definition size_itself_int x := Z.of_nat (size_itself x)

(* NB: the corresponding sail type is forall n. atom(n) -> itself(n),
   the actual integer is ignored. *)

val make_the_value : forall n. Z -> itself n
Definition inline make_the_value x := the_value
*)

Fixpoint wordFromBitlist_rev l : word (length l) :=
match l with
| [] => WO
| b::t => WS b (wordFromBitlist_rev t)
end.
Definition wordFromBitlist l : word (length l) :=
  nat_cast _ (List.rev_length l) (wordFromBitlist_rev (List.rev l)).

Local Open Scope nat.

Fixpoint nat_diff {T : nat -> Type} n m {struct n} :
forall
 (lt : forall p, T n -> T (n + p))
 (eq : T m -> T m)
 (gt : forall p, T (m + p) -> T m), T n -> T m :=
(match n, m return (forall p, T n -> T (n + p)) -> (T m -> T m) -> (forall p, T (m + p) -> T m) -> T n -> T m with
| O, O => fun lt eq gt => eq
| S n', O => fun lt eq gt => gt _
| O, S m' => fun lt eq gt => lt _
| S n', S m' => @nat_diff (fun x => T (S x)) n' m'
end).

Definition fit_bbv_word {n m} : word n -> word m :=
nat_diff n m
 (fun p w => nat_cast _ (Nat.add_comm _ _) (extz w p))
 (fun w => w)
 (fun p w => split2 _ _ (nat_cast _ (Nat.add_comm _ _) w)).

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
  isPositive : a >=? 0 = true
}.

(* Definitions in the context that involve proof for other constraints can
   break some of the constraint solving tactics, so prune definition bodies
   down to integer types. *)
Ltac not_Z_bool ty := match ty with Z => fail 1 | bool => fail 1 | _ => idtac end.
Ltac clear_non_Z_bool_defns := 
  repeat match goal with H := _ : ?X |- _ => not_Z_bool X; clearbody H end.
Ltac clear_irrelevant_defns :=
repeat match goal with X := _ |- _ =>
  match goal with |- context[X] => idtac end ||
  match goal with _ : context[X] |- _ => idtac end || clear X
end.

Lemma lift_bool_exists (l r : bool) (P : bool -> Prop) :
  (l = r -> exists x, P x) ->
  (exists x, l = r -> P x).
intro H.
destruct (Bool.bool_dec l r) as [e | ne].
* destruct (H e) as [x H']; eauto.
* exists true; tauto.
Qed.

Lemma ArithFact_mword (a : Z) (w : mword a) : ArithFact (a >=? 0).
constructor.
destruct a.
* auto with zarith.
* auto using Z.le_ge, Zle_0_pos.
* destruct w.
Qed.
(* Remove constructor from ArithFact(P)s and if they're used elsewhere
   in the context create a copy that rewrites will work on. *)
Ltac unwrap_ArithFacts :=
  let gen X :=
    let Y := fresh "Y" in pose X as Y; generalize Y
  in
  let unwrap H :=
      let H' := fresh H in case H as [H']; clear H;
      match goal with
      | _ :  context[H'] |- _ => gen H'
      | _ := context[H'] |- _ => gen H'
      |   |- context[H']      => gen H'
      | _ => idtac
      end
  in
  repeat match goal with
  | H:(ArithFact _) |- _ => unwrap H
  | H:(ArithFactP _) |- _ => unwrap H
  end.
Ltac unbool_comparisons :=
  repeat match goal with
  | H:@eq bool _ _ -> @ex bool _ |- _ => apply lift_bool_exists in H; destruct H
  | H:@ex Z _ |- _ => destruct H
  (* Omega doesn't know about In, but can handle disjunctions. *)
  | H:context [member_Z_list _ _ = true] |- _ => rewrite member_Z_list_In in H
  | H:context [In ?x (?y :: ?t)] |- _ => change (In x (y :: t)) with (y = x \/ In x t) in H
  | H:context [In ?x []] |- _ => change (In x []) with False in H
  | H:?v = true |- _ => is_var v; subst v
  | H:?v = false |- _ => is_var v; subst v
  | H:true = ?v |- _ => is_var v; subst v
  | H:false = ?v |- _ => is_var v; subst v
  | H:_ /\ _ |- _ => destruct H
  | H:context [Z.geb _ _] |- _ => rewrite Z.geb_leb in H
  | H:context [Z.gtb _ _] |- _ => rewrite Z.gtb_ltb in H
  | H:context [Z.leb _ _ = true] |- _ => rewrite Z.leb_le in H
  | H:context [Z.ltb _ _ = true] |- _ => rewrite Z.ltb_lt in H
  | H:context [Z.eqb _ _ = true] |- _ => rewrite Z.eqb_eq in H
  | H:context [Z.leb _ _ = false] |- _ => rewrite Z.leb_gt in H
  | H:context [Z.ltb _ _ = false] |- _ => rewrite Z.ltb_ge in H
  | H:context [Z.eqb _ _ = false] |- _ => rewrite Z.eqb_neq in H
  | H:context [orb _ _ = true] |- _ => rewrite Bool.orb_true_iff in H
  | H:context [orb _ _ = false] |- _ => rewrite Bool.orb_false_iff in H
  | H:context [andb _ _ = true] |- _ => rewrite Bool.andb_true_iff in H
  | H:context [andb _ _ = false] |- _ => rewrite Bool.andb_false_iff in H
  | H:context [negb _ = true] |- _ => rewrite Bool.negb_true_iff in H
  | H:context [negb _ = false] |- _ => rewrite Bool.negb_false_iff in H
  | H:context [Bool.eqb _ ?r = true] |- _ => rewrite Bool.eqb_true_iff in H;
                                             try (is_var r; subst r)
  | H:context [Bool.eqb _ _ = false] |- _ => rewrite Bool.eqb_false_iff in H
  | H:context [generic_eq _ _ = true] |- _ => apply generic_eq_true in H
  | H:context [generic_eq _ _ = false] |- _ => apply generic_eq_false in H
  | H:context [generic_neq _ _ = true] |- _ => apply generic_neq_true in H
  | H:context [generic_neq _ _ = false] |- _ => apply generic_neq_false in H
  | H:context [_ <> true] |- _ => rewrite Bool.not_true_iff_false in H
  | H:context [_ <> false] |- _ => rewrite Bool.not_false_iff_true in H
  | H:context [@eq bool ?l ?r] |- _ =>
    lazymatch r with
    | true => fail
    | false => fail
    | _ => rewrite (Bool.eq_iff_eq_true l r) in H
    end
  end.
Ltac unbool_comparisons_goal :=
  repeat match goal with
  (* Important to have these early in the list - setoid_rewrite can
     unfold member_Z_list. *)
  | |- context [member_Z_list _ _ = true] => rewrite member_Z_list_In
  | |- context [In ?x (?y :: ?t)] => change (In x (y :: t)) with (y = x \/ In x t) 
  | |- context [In ?x []] => change (In x []) with False
  | |- context [Z.geb _ _] => setoid_rewrite Z.geb_leb
  | |- context [Z.gtb _ _] => setoid_rewrite Z.gtb_ltb
  | |- context [Z.leb _ _ = true] => setoid_rewrite Z.leb_le
  | |- context [Z.ltb _ _ = true] => setoid_rewrite Z.ltb_lt
  | |- context [Z.eqb _ _ = true] => setoid_rewrite Z.eqb_eq
  | |- context [Z.leb _ _ = false] => setoid_rewrite Z.leb_gt
  | |- context [Z.ltb _ _ = false] => setoid_rewrite Z.ltb_ge
  | |- context [Z.eqb _ _ = false] => setoid_rewrite Z.eqb_neq
  | |- context [orb _ _ = true] => setoid_rewrite Bool.orb_true_iff
  | |- context [orb _ _ = false] => setoid_rewrite Bool.orb_false_iff
  | |- context [andb _ _ = true] => setoid_rewrite Bool.andb_true_iff
  | |- context [andb _ _ = false] => setoid_rewrite Bool.andb_false_iff
  | |- context [negb _ = true] => setoid_rewrite Bool.negb_true_iff
  | |- context [negb _ = false] => setoid_rewrite Bool.negb_false_iff
  | |- context [Bool.eqb _ _ = true] => setoid_rewrite Bool.eqb_true_iff
  | |- context [Bool.eqb _ _ = false] => setoid_rewrite Bool.eqb_false_iff
  | |- context [generic_eq _ _ = true] => apply generic_eq_true
  | |- context [generic_eq _ _ = false] => apply generic_eq_false
  | |- context [generic_neq _ _ = true] => apply generic_neq_true
  | |- context [generic_neq _ _ = false] => apply generic_neq_false
  | |- context [_ <> true] => setoid_rewrite Bool.not_true_iff_false
  | |- context [_ <> false] => setoid_rewrite Bool.not_false_iff_true
  | |- context [@eq bool _ ?r] =>
    lazymatch r with
    | true => fail
    | false => fail
    | _ => setoid_rewrite Bool.eq_iff_eq_true
    end
  end.

(* Split up dependent pairs to get at proofs of properties *)
Ltac extract_properties :=
  (* Properties of local definitions *)
  repeat match goal with H := context[projT1 ?X] |- _ =>
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    destruct X as [x Hx] in *;
    change (projT1 (existT _ x Hx)) with x in * end;
  (* Properties in the goal *)
  repeat match goal with |- context [projT1 ?X] =>
    let x := fresh "x" in
    let Hx := fresh "Hx" in
    destruct X as [x Hx] in *;
    change (projT1 (existT _ x Hx)) with x in * end;
  (* Properties with proofs embedded by build_ex; uses revert/generalize
     rather than destruct because it seemed to be more efficient, but
     some experimentation would be needed to be sure. 
  repeat (
     match goal with H:context [@build_ex ?T ?n ?P ?prf] |- _ =>
     let x := fresh "x" in
     let zz := constr:(@build_ex T n P prf) in
     revert dependent H(*; generalize zz; intros*)
     end;
     match goal with |- context [@build_ex ?T ?n ?P ?prf] =>
     let x := fresh "x" in
     let zz := constr:(@build_ex T n P prf) in
     generalize zz as x
     end;
    intros).*)
  repeat match goal with _:context [projT1 ?X] |- _ =>
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
Ltac dump_context :=
  repeat match goal with
  | H:=?X |- _ => idtac H ":=" X; fail
  | H:?X |- _ => idtac H ":" X; fail end;
  match goal with |- ?X => idtac "Goal:" X end.
Ltac split_cases :=
  repeat match goal with
  |- context [match ?X with _ => _ end] => destruct X
  end.
Lemma True_left {P:Prop} : (True /\ P) <-> P.
tauto.
Qed.
Lemma True_right {P:Prop} : (P /\ True) <-> P.
tauto.
Qed.

(* Turn exists into metavariables like eexists, except put in dummy values when
   the variable is unused.  This is used so that we can use eauto with a low
   search bound that doesn't include the exists.  (Not terribly happy with
   how this works...) *)
Ltac drop_Z_exists :=
repeat
  match goal with |- @ex Z ?p =>
   let a := eval hnf in (p 0) in
   let b := eval hnf in (p 1) in
   match a with b => exists 0 | _ => eexists end
  end.
(*
  match goal with |- @ex Z (fun x => @?p x) =>
   let xx := fresh "x" in
   evar (xx : Z);
   let a := eval hnf in (p xx) in
   match a with context [xx] => eexists | _ => exists 0 end;
   instantiate (xx := 0);
   clear xx
  end.
*)
(* For boolean solving we just use plain metavariables *)
Ltac drop_bool_exists :=
repeat match goal with |- @ex bool _ => eexists end.

(* The linear solver doesn't like existentials. *)
Ltac destruct_exists :=
  repeat match goal with H:@ex Z _ |- _ => destruct H end;
  repeat match goal with H:@ex bool _ |- _ => destruct H end.

(* The ASL to Sail translator sometimes puts constraints of the form
   p | not(q) into function signatures, then the body case splits on q.
   The filter_disjunctions tactic simplifies hypotheses by obtaining p. *)

Lemma truefalse : true = false <-> False.
intuition.
Qed.
Lemma falsetrue : false = true <-> False.
intuition.
Qed.
Lemma or_False_l P : False \/ P <-> P.
intuition.
Qed.
Lemma or_False_r P : P \/ False <-> P.
intuition.
Qed.

Ltac filter_disjunctions :=
  repeat match goal with
  | H1:?P \/ ?t1 = ?t2, H2: ?t3 = ?t4 |- _ =>
    (* I used to use non-linear matching above, but Coq is happy to match up
       to conversion, including more unfolding than we normally do. *)
    constr_eq t1 t3; constr_eq t2 t4; clear H1
  | H1:context [?P \/ ?t = true], H2: ?t = false |- _ => is_var t; rewrite H2 in H1
  | H1:context [?P \/ ?t = false], H2: ?t = true |- _ => is_var t; rewrite H2 in H1
  | H1:context [?t = true \/ ?P], H2: ?t = false |- _ => is_var t; rewrite H2 in H1
  | H1:context [?t = false \/ ?P], H2: ?t = true |- _ => is_var t; rewrite H2 in H1
  end;
  rewrite ?truefalse, ?falsetrue, ?or_False_l, ?or_False_r in *;
  (* We may have uncovered more conjunctions *)
  repeat match goal with H:and _ _ |- _ => destruct H end.

(* Turn x := if _ then ... into x = ... \/ x = ... *)

Ltac Z_if_to_or :=
  repeat match goal with x := ?t : Z |- _ =>
    let rec build_goal t :=
      match t with
      | if _ then ?y else ?z =>
        let Hy := build_goal y in
        let Hz := build_goal z in
        constr:(Hy \/ Hz)
      | ?y => constr:(x = y)
      end
    in
    let rec split_hyp t :=
      match t with
      | if ?b then ?y else ?z =>
        destruct b in x; [split_hyp y| split_hyp z]
      | _ => idtac
      end
    in
    let g := build_goal t in
    assert g by (clear -x; split_hyp t; auto);
    clearbody x
  end.

(* Once we've done everything else, get rid of irrelevant bool and Z bindings
   to help the brute force solver *)
Ltac clear_irrelevant_bindings :=
  repeat
    match goal with
    | b : bool |- _ =>
      lazymatch goal with
      | _ : context [b] |- _ => fail
      | |- context [b] => fail
      | _ => clear b
      end
    | x : Z |- _ =>
      lazymatch goal with
      | _ : context [x] |- _ => fail
      | |- context [x] => fail
      | _ => clear x
      end
    | H:?x |- _ =>
      let s := type of x in
      lazymatch s with
      | Prop =>
        match x with
        | context [?v] => is_var v; fail 1
        | _ => clear H
        end
      | _ => fail
      end
    end.

(* Currently, the ASL to Sail translation produces some constraints of the form
   P \/ x = true, P \/ x = false, which are simplified by the tactic below.  In
   future the translation is likely to be cleverer, and this won't be
   necessary. *)
(* TODO: remove duplication with filter_disjunctions *)
Lemma remove_unnecessary_casesplit {P:Prop} {x} :
  P \/ x = true -> P \/ x = false -> P.
  intuition congruence.
Qed.
Lemma remove_eq_false_true {P:Prop} {x} :
  x = true -> P \/ x = false -> P.
intros H1 [H|H]; congruence.
Qed.
Lemma remove_eq_true_false {P:Prop} {x} :
  x = false -> P \/ x = true -> P.
intros H1 [H|H]; congruence.
Qed.
Ltac remove_unnecessary_casesplit :=
repeat match goal with
| H1 : ?P \/ ?v = true, H2 : ?v = true |- _ => clear H1
| H1 : ?P \/ ?v = true, H2 : ?v = false |- _ => apply (remove_eq_true_false H2) in H1
| H1 : ?P \/ ?v = false, H2 : ?v = false |- _ => clear H1
| H1 : ?P \/ ?v = false, H2 : ?v = true |- _ => apply (remove_eq_false_true H2) in H1
| H1 : ?P \/ ?v1 = true, H2 : ?P \/ ?v2 = false |- _ =>
  constr_eq v1 v2;
  is_var v1;
  apply (remove_unnecessary_casesplit H1) in H2;
  clear H1
  (* There are worse cases where the hypotheses are different, so we actually
     do the casesplit *)
| H1 : _ \/ ?v = true, H2 : _ \/ ?v = false |- _ =>
  is_var v;
  destruct v;
  [ clear H1; destruct H2; [ | congruence ]
  | clear H2; destruct H1; [ | congruence ]
  ]
end;
(* We may have uncovered more conjunctions *)
repeat match goal with H:and _ _ |- _ => destruct H end.

(* Remove details of embedded proofs. *)
Ltac generalize_embedded_proofs :=
  repeat match goal with H:context [?X] |- _ =>
    match type of X with
    | ArithFact  _ => generalize dependent X
    | ArithFactP _ => generalize dependent X
    end
  end;
  intros.

Lemma iff_equal_l {T:Type} {P:Prop} {x:T} : (x = x <-> P) -> P.
tauto.
Qed.
Lemma iff_equal_r {T:Type} {P:Prop} {x:T} : (P <-> x = x) -> P.
tauto.
Qed.

Lemma iff_known_l {P Q : Prop} : P -> P <-> Q -> Q.
tauto.
Qed.
Lemma iff_known_r {P Q : Prop} : P -> Q <-> P -> Q.
tauto.
Qed.

Ltac clean_up_props :=
  repeat match goal with
  (* I did try phrasing these as rewrites, but Coq was oddly reluctant to use them *)
  | H:?x = ?x <-> _ |- _ => apply iff_equal_l in H
  | H:_ <-> ?x = ?x |- _ => apply iff_equal_r in H
  | H:context[true = false] |- _ => rewrite truefalse in H
  | H:context[false = true] |- _ => rewrite falsetrue in H
  | H1:?P <-> False, H2:context[?Q] |- _ => constr_eq P Q; rewrite -> H1 in H2
  | H1:False <-> ?P, H2:context[?Q] |- _ => constr_eq P Q; rewrite <- H1 in H2
  | H1:?P, H2:?Q <-> ?R |- _ => constr_eq P Q; apply (iff_known_l H1) in H2
  | H1:?P, H2:?R <-> ?Q |- _ => constr_eq P Q; apply (iff_known_r H1) in H2
  | H:context[_ \/ False] |- _ => rewrite or_False_r in H
  | H:context[False \/ _] |- _ => rewrite or_False_l in H
  end;
  remove_unnecessary_casesplit.

Ltac prepare_for_solver :=
(*dump_context;*)
 generalize_embedded_proofs;
 clear_irrelevant_defns;
 clear_non_Z_bool_defns;
 autounfold with sail in * |- *; (* You can add Hint Unfold ... : sail to let lia see through fns *)
 split_cases;
 extract_properties;
 repeat match goal with w:mword ?n |- _ => apply ArithFact_mword in w end;
 unwrap_ArithFacts;
 destruct_exists;
 unbool_comparisons;
 unbool_comparisons_goal;
 repeat match goal with H:and _ _ |- _ => destruct H end;
 remove_unnecessary_casesplit;
 reduce_list_lengths;
 reduce_pow;
 filter_disjunctions;
 Z_if_to_or;
 clear_irrelevant_bindings;
 subst;
 clean_up_props.

Lemma trivial_range {x : Z} : ArithFact ((x <=? x <=? x)).
constructor.
auto using Z.leb_refl with bool.
Qed.

Lemma ArithFact_self_proof {P} : forall x : {y : Z & ArithFact (P y)}, ArithFact (P (projT1 x)).
intros [x H].
exact H.
Qed.

Lemma ArithFactP_self_proof {P} : forall x : {y : Z & ArithFactP (P y)}, ArithFactP (P (projT1 x)).
intros [x H].
exact H.
Qed.

Ltac fill_in_evar_eq :=
 match goal with |- ArithFact (?x =? ?y) =>
   (is_evar x || is_evar y);
   (* compute to allow projections to remove proofs that might not be allowed in the evar *)
(* Disabled because cbn may reduce definitions, even after clearbody
   let x := eval cbn in x in
   let y := eval cbn in y in*)
   idtac "Warning: unknown equality constraint"; constructor; exact (Z.eqb_refl _ : x =? y = true) end.

Ltac bruteforce_bool_exists :=
match goal with
| |- exists _ : bool,_ => solve [ exists true; bruteforce_bool_exists
                                | exists false; bruteforce_bool_exists ]
| _ => tauto
end.

Lemma or_iff_cong : forall A B C D, A <-> B -> C <-> D -> A \/ C <-> B \/ D.
intros.
tauto.
Qed.

Lemma and_iff_cong : forall A B C D, A <-> B -> C <-> D -> A /\ C <-> B /\ D.
intros.
tauto.
Qed.

Ltac solve_euclid :=
repeat match goal with
| |- context [ZEuclid.modulo ?x ?y] =>
  specialize (ZEuclid.div_mod x y);
  specialize (ZEuclid.mod_always_pos x y);
  generalize (ZEuclid.modulo x y);
  generalize (ZEuclid.div x y);
  intros
| |- context [ZEuclid.div ?x ?y] =>
  specialize (ZEuclid.div_mod x y);
  specialize (ZEuclid.mod_always_pos x y);
  generalize (ZEuclid.modulo x y);
  generalize (ZEuclid.div x y);
  intros
end;
nia.
(* Try to get the linear arithmetic solver to do booleans. *)

Lemma b2z_true x : x = true <-> Z.b2z x = 1.
destruct x; compute; split; congruence.
Qed.

Lemma b2z_false x : x = false <-> Z.b2z x = 0.
destruct x; compute; split; congruence.
Qed.

Lemma b2z_tf x : 0 <= Z.b2z x <= 1.
destruct x; simpl; lia.
Qed.

Lemma b2z_andb a b :
  Z.b2z (a && b) = Z.min (Z.b2z a) (Z.b2z b).
destruct a,b; reflexivity.
Qed.
Lemma b2z_orb a b :
  Z.b2z (a || b) = Z.max (Z.b2z a) (Z.b2z b).
destruct a,b; reflexivity.
Qed.

Lemma b2z_eq : forall a b, Z.b2z a = Z.b2z b <-> a = b.
intros [|] [|];
simpl;
intuition try congruence.
Qed.

Lemma b2z_negb x : Z.b2z (negb x) = 1 - Z.b2z x.
  destruct x ; reflexivity.
Qed.

Ltac bool_to_Z :=
  subst;
  rewrite ?truefalse, ?falsetrue, ?or_False_l, ?or_False_r in *;
  (* I did try phrasing these as rewrites, but Coq was oddly reluctant to use them *)
  repeat match goal with
  | H:?x = ?x <-> _ |- _ => apply iff_equal_l in H
  | H:_ <-> ?x = ?x |- _ => apply iff_equal_r in H
  end;
  repeat match goal with
  | H:context [negb ?v] |- _ => rewrite b2z_negb in H
  | |- context [negb ?v]     => rewrite b2z_negb 
  |  H:context [?v = true] |- _  => is_var v; rewrite (b2z_true v) in *
  | |- context [?v = true]       => is_var v; rewrite (b2z_true v) in *
  |  H:context [?v = false] |- _ => is_var v; rewrite (b2z_false v) in *
  | |- context [?v = false]      => is_var v; rewrite (b2z_false v) in *
  | H:context [?v = ?w] |- _ => rewrite <- (b2z_eq v w) in H
  | |- context [?v = ?w]     => rewrite <- (b2z_eq v w)
  | H:context [Z.b2z (?v && ?w)] |- _ => rewrite (b2z_andb v w) in H
  | |- context [Z.b2z (?v && ?w)]     => rewrite (b2z_andb v w)
  | H:context [Z.b2z (?v || ?w)] |- _ => rewrite (b2z_orb v w) in H
  | |- context [Z.b2z (?v || ?w)]     => rewrite (b2z_orb v w)
  end;
  change (Z.b2z true) with 1 in *;
  change (Z.b2z false) with 0 in *;
  repeat match goal with
  | _:context [Z.b2z ?v] |- _ => generalize (b2z_tf v); generalize dependent (Z.b2z v)
  | |- context [Z.b2z ?v]     => generalize (b2z_tf v); generalize dependent (Z.b2z v)
  end.
Ltac solve_bool_with_Z :=
  bool_to_Z;
  intros;
  lia.

(* A more ambitious brute force existential solver. *)

Ltac guess_ex_solver :=
  match goal with
  | |- @ex bool ?t =>
    match t with
    | context [@eq bool ?b _] =>
      solve [ exists b; guess_ex_solver
            | exists (negb b); rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff;
              guess_ex_solver ]
    end
(*  | b : bool |- @ex bool _ => exists b; guess_ex_solver
  | b : bool |- @ex bool _ =>
    exists (negb b); rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff;
    guess_ex_solver*)
  | |- @ex bool _ => exists true; guess_ex_solver
  | |- @ex bool _ => exists false; guess_ex_solver
  | x : ?ty |- @ex ?ty _ => exists x; guess_ex_solver
  | _ => solve [tauto | eauto 3 with zarith sail | solve_bool_with_Z | lia]
  end.

(* A straightforward solver for simple problems like

   exists ..., _ = true \/ _ = false /\ _ = true <-> _ = true \/ _ = true
*)

Ltac form_iff_true :=
repeat match goal with
| |- ?l <-> _ = true =>
  let rec aux t :=
      match t with
      | _ = true \/ _ = true => rewrite <- Bool.orb_true_iff
      | _ = true /\ _ = true => rewrite <- Bool.andb_true_iff
      | _ = false => rewrite <- Bool.negb_true_iff
      | ?l \/ ?r => aux l || aux r
      | ?l /\ ?r => aux l || aux r
      end
  in aux l
       end.
Ltac simple_split_iff :=
  repeat
    match goal with
    | |- _ /\ _ <-> _ /\ _ => apply and_iff_cong
    | |- _ \/ _ <-> _ \/ _ => apply or_iff_cong
    end.
Ltac simple_ex_iff :=
  match goal with
  | |- @ex _ _ => eexists; simple_ex_iff
  | |- _ <-> _ =>
    symmetry;
    simple_split_iff;
    form_iff_true;
    solve [apply iff_refl | eassumption]
  end.

(* Another attempt at similar goals, this time allowing for conjuncts to move
  around, and filling in integer existentials and redundant boolean ones.
   TODO: generalise / combine with simple_ex_iff. *)

Ltac ex_iff_construct_bool_witness :=
let rec search x y :=
  lazymatch y with
  | x => constr:(true)
  | ?y1 /\ ?y2 =>
    let b1 := search x y1 in
    let b2 := search x y2 in
    constr:(orb b1 b2)
  | _ => constr:(false)
  end
in
let rec make_clause x :=
  lazymatch x with
  | ?l = true => l
  | ?l = false => constr:(negb l)
  | @eq Z ?l ?n => constr:(Z.eqb l n)
  | ?p \/ ?q =>
    let p' := make_clause p in
    let q' := make_clause q in
    constr:(orb p' q')
  | _ => fail
  end in
let add_clause x xs :=
  let l := make_clause x in
  match xs with
  | true => l
  | _ => constr:(andb l xs)
  end
in
let rec construct_ex l r x :=
  lazymatch l with
  | ?l1 /\ ?l2 =>
    let y := construct_ex l1 r x in
    construct_ex l2 r y
  | _ =>
   let present := search l r in
   lazymatch eval compute in present with true => x | _ => add_clause l x end
  end
in
let witness := match goal with
| |- ?l <-> ?r => construct_ex l r constr:(true)
end in
instantiate (1 := witness).

Ltac ex_iff_fill_in_ints :=
  let rec search l r y :=
    match y with
    | l = r => idtac
    | ?v = r => is_evar v; unify v l
    | ?y1 /\ ?y2 => first [search l r y1 | search l r y2]
    | _ => fail
    end
  in
  match goal with
  | |- ?l <-> ?r =>
    let rec traverse l :=
    lazymatch l with
    | ?l1 /\ ?l2 =>
      traverse l1; traverse l2
    | @eq Z ?x ?y => search x y r
    | _ => idtac
    end
    in traverse l
  end.

Ltac ex_iff_fill_in_bools :=
  let rec traverse t :=
    lazymatch t with
    | ?v = ?t => try (is_evar v; unify v t)
    | ?p /\ ?q => traverse p; traverse q
    | _ => idtac
    end
  in match goal with
  | |- _ <-> ?r => traverse r
  end.

Ltac conjuncts_iff_solve :=
  ex_iff_fill_in_ints;
  ex_iff_construct_bool_witness;
  ex_iff_fill_in_bools;
  unbool_comparisons_goal;
  clear;
  intuition.

Ltac ex_iff_solve :=
  match goal with
  | |- @ex _ _ => eexists; ex_iff_solve
  (* Range constraints are attached to the right *)
  | |- _ /\ _ => split; [ex_iff_solve | lia]
  | |- _ <-> _ => conjuncts_iff_solve || (symmetry; conjuncts_iff_solve)
  end.


Lemma iff_false_left {P Q R : Prop} : (false = true) <-> Q -> (false = true) /\ P <-> Q /\ R.
intuition.
Qed.

(* Very simple proofs for trivial arithmetic.  Preferable to running omega/lia because
   they can get bogged down if they see large definitions; should also guarantee small
   proof terms. *)
Lemma Z_compare_lt_eq : Lt = Eq -> False. congruence. Qed.
Lemma Z_compare_lt_gt : Lt = Gt -> False. congruence. Qed.
Lemma Z_compare_eq_lt : Eq = Lt -> False. congruence. Qed.
Lemma Z_compare_eq_gt : Eq = Gt -> False. congruence. Qed.
Lemma Z_compare_gt_lt : Gt = Lt -> False. congruence. Qed.
Lemma Z_compare_gt_eq : Gt = Eq -> False. congruence. Qed.
Ltac z_comparisons :=
  (* Don't try terms with variables - reduction may be expensive *)
  match goal with |- context[?x] => is_var x; fail 1 | |- _ => idtac end;
  solve [
    exact eq_refl
  | exact Z_compare_lt_eq
  | exact Z_compare_lt_gt
  | exact Z_compare_eq_lt
  | exact Z_compare_eq_gt
  | exact Z_compare_gt_lt
  | exact Z_compare_gt_eq
  ].
                                                                                   
Ltac bool_ex_solve :=
match goal with H : ?l = ?v -> @ex _ _ |- @ex _ _ =>
     match v with true => idtac | false => idtac end;
     destruct l;
     repeat match goal with H:?X = ?X -> _ |- _ => specialize (H eq_refl) end;
     repeat match goal with H:@ex _ _ |- _ => destruct H end;
     unbool_comparisons;
     guess_ex_solver
end.

(* Solve a boolean equality goal which is just rearranged clauses (e.g, at the
   end of the clause_matching_bool_solver, below. *)
Ltac bruteforce_bool_eq :=
  lazymatch goal with
  | |- _ && ?l1 = _ => idtac l1; destruct l1; rewrite ?Bool.andb_true_l, ?Bool.andb_true_r, ?Bool.andb_false_l, ?Bool.andb_false_r; bruteforce_bool_eq
  | |- ?l = _ => reflexivity
  end.

Ltac clause_matching_bool_solver :=
(* Do the left hand and right hand clauses have the same shape? *)
let rec check l r :=
    lazymatch l with
    | ?l1 || ?l2 =>
      lazymatch r with ?r1 || ?r2 => check l1 r1; check l2 r2 end
    | ?l1 =? ?l2 =>
      lazymatch r with ?r1 =? ?r2 => check l1 r1; check l2 r2 end
    | _ => is_evar l + constr_eq l r
    end
in
(* Rebuild remaining rhs, dropping extra "true"s. *)
let rec add_clause l r :=
  match l with
  | true => r
  | _ => match r with true => l | _ => constr:(l && r) end
  end
in
(* Find a clause in r matching l, use unify to instantiate evars, return rest of r *)
let rec find l r :=
    lazymatch r with
    | ?r1 && ?r2 =>
      match l with
      | _ => let r1' := find l r1 in add_clause r1' r2
      | _ => let r2' := find l r2 in add_clause r1 r2'
      end
    | _ => constr:(ltac:(check l r; unify l r; exact true))
    end
in
(* For each clause in the lhs, find a matching clause in rhs, fill in
   remaining evar with left over.  TODO: apply to goals without an evar clause *)
match goal with
  | |- @ex _ _ => eexists; clause_matching_bool_solver
  | |- _ = _ /\ _ <= _ <= _ => split; [clause_matching_bool_solver | lia]
  | |- ?l = ?r =>
  let rec clause l r :=
      match l with
      | ?l1 && ?l2 =>
        let r2 := clause l1 r in clause l2 r2
      | _ => constr:(ltac:(is_evar l; exact r))
      | _ => find l r
      end
  in let r' := clause l r in
     instantiate (1 := r');
     rewrite ?Bool.andb_true_l, ?Bool.andb_assoc;
     bruteforce_bool_eq
end.



(* Redefine this to add extra solver tactics *)
Ltac sail_extra_tactic := fail.

Ltac main_solver :=
 solve
 [ apply ArithFact_mword; assumption
 | z_comparisons
 | lia
   (* Try sail hints before dropping the existential *)
 | subst; eauto 3 with zarith sail
   (* The datatypes hints give us some list handling, esp In *)
 | subst; drop_Z_exists;
   repeat match goal with |- and _ _ => split end;
   eauto 3 with datatypes zarith sail
 | subst; match goal with |- context [ZEuclid.div] => solve_euclid
                        | |- context [ZEuclid.modulo] => solve_euclid
   end
 | match goal with |- context [Z.mul] => nia end
 (* If we have a disjunction from a set constraint on a variable we can often
    solve a goal by trying them (admittedly this is quite heavy handed...) *)
 | subst; drop_Z_exists;
   let aux x :=
    is_var x;
    intuition (subst;auto with datatypes)
   in
   match goal with
   | _:(@eq Z _ ?x) \/ (@eq Z _ ?x) \/ _ |- context[?x] => aux x
   | _:(@eq Z ?x _) \/ (@eq Z ?x _) \/ _ |- context[?x] => aux x
   | _:(@eq Z _ ?x) \/ (@eq Z _ ?x) \/ _, _:@eq Z ?y (ZEuclid.div ?x _) |- context[?y] => is_var x; aux y
   | _:(@eq Z ?x _) \/ (@eq Z ?x _) \/ _, _:@eq Z ?y (ZEuclid.div ?x _) |- context[?y] => is_var x; aux y
   end
 (* Booleans - and_boolMP *)
 | solve_bool_with_Z
 | simple_ex_iff
 | ex_iff_solve
 | drop_bool_exists; solve [eauto using iff_refl, or_iff_cong, and_iff_cong | intuition]
 | match goal with |- (forall l r:bool, _ -> _ -> exists _ : bool, _) =>
     let r := fresh "r" in
     let H1 := fresh "H" in
     let H2 := fresh "H" in
     intros [|] r H1 H2;
     let t2 := type of H2 in
     match t2 with
     | ?b = ?b -> _ =>
       destruct (H2 eq_refl);
       repeat match goal with H:@ex _ _ |- _ => destruct H end;
       simple_ex_iff
     | ?b = _ -> _ =>
       repeat match goal with H:@ex _ _ |- _ => destruct H end;
       clear H2;
       repeat match goal with
              | |- @ex bool _ => exists b
              | |- @ex Z _ => exists 0
              end;
       intuition
     end
   end
 | match goal with |- (forall l r:bool, _ -> _ -> @ex _ _) =>
     let H1 := fresh "H" in
     let H2 := fresh "H" in
     intros [|] [|] H1 H2;
     repeat match goal with H:?X = ?X -> _ |- _ => specialize (H eq_refl) end;
     repeat match goal with H:@ex _ _ |- _ => destruct H end;
     guess_ex_solver
   end
(* While firstorder was quite effective at dealing with existentially quantified
   goals from boolean expressions, it attempts lazy normalization of terms,
   which blows up on integer comparisons with large constants.
 | match goal with |- context [@eq bool _ _] =>
     (* Don't use auto for the fallback to keep runtime down *)
     firstorder fail
   end*)
 | bool_ex_solve
 | clause_matching_bool_solver
 | match goal with |- @ex _ _ => guess_ex_solver end
 | sail_extra_tactic
 | idtac "Unable to solve constraint"; dump_context; fail
 ].

(* Omega can get upset by local definitions that are projections from value/proof pairs.
   Complex goals can use prepare_for_solver to extract facts; this tactic can be used
   for simpler proofs without using prepare_for_solver. *)
Ltac simple_omega :=
  repeat match goal with
  H := projT1 _ |- _ => clearbody H
  end; lia.

Ltac solve_unknown :=
  match goal with
  | |- (ArithFact (?x ?y)) =>
    is_evar x;
    idtac "Warning: unknown constraint";
    let t := type of y in
    unify x (fun (_ : t) => true);
    exact (Build_ArithFactP _ eq_refl : ArithFact true)
  | |- (ArithFactP (?x ?y)) =>
    is_evar x;
    idtac "Warning: unknown constraint";
    let t := type of y in
    unify x (fun (_ : t) => True);
    exact (Build_ArithFactP _ I : ArithFactP True)
  end.

(* Solving straightforward and_boolMP / or_boolMP goals *)

Lemma default_and_proof l r r' :
  (l = true -> r' = r) ->
  l && r' = l && r.
  intro H.
destruct l; [specialize (H eq_refl) | clear H ]; auto.
Qed.

Lemma default_and_proof2 l l' r r' :
  l' = l ->
  (l = true -> r' = r) ->
  l' && r' = l && r.
intros; subst.
auto using default_and_proof.
Qed.

Lemma default_or_proof l r r' :
  (l = false -> r' = r) ->
  l || r' = l || r.
  intro H.
destruct l; [clear H | specialize (H eq_refl) ]; auto.
Qed.

Lemma default_or_proof2 l l' r r' :
  l' = l ->
  (l = false -> r' = r) ->
  l' || r' = l || r.
intros; subst.
auto using default_or_proof.
Qed.

Ltac default_andor :=
  intros; constructor; intros;
  repeat match goal with
  | H:@ex _ _ |- _ => destruct H
  | H:@eq bool _ _ -> @ex bool _ |- _ => apply lift_bool_exists in H
   end;
  repeat match goal with |- @ex _ _ => eexists end;
  rewrite ?Bool.eqb_true_iff, ?Bool.eqb_false_iff in *;
  match goal with
  | H:?v = true -> _ |- _ = ?v && _ => solve [eapply default_and_proof; eauto 2]
  | H:?v = true -> _ |- _ = ?v && _ => solve [eapply default_and_proof2; eauto 2]
  | H:?v = false -> _ |- _ = ?v || _ => solve [eapply default_or_proof; eauto 2]
  | H:?v = false -> _ |- _ = ?v || _ => solve [eapply default_or_proof2; eauto 2]
  | H:?v = true -> _ |- _ = ?v && _ => solve [rewrite Bool.andb_comm; eapply default_and_proof; eauto 2]
  | H:?v = true -> _ |- _ = ?v && _ => solve [rewrite Bool.andb_comm; eapply default_and_proof2; eauto 2]
  | H:?v = false -> _ |- _ = ?v || _ => solve [rewrite Bool.orb_comm; eapply default_or_proof; eauto 2]
  | H:?v = false -> _ |- _ = ?v || _ => solve [rewrite Bool.orb_comm; eapply default_or_proof2; eauto 2]
  end.

(* Solving simple and_boolMP / or_boolMP goals where unknown booleans
   have been merged together. *)

Ltac squashed_andor_solver :=
  clear;
  match goal with |- forall l r : bool, ArithFactP (_ -> _ -> _) => idtac end;
  intros l r; constructor; intros;
  let func := match goal with |- context[?f l r] => f end in
  match goal with
  | H1 : @ex _ _, H2 : l = _ -> @ex _ _ |- _ =>
    let x1 := fresh "x1" in
    let x2 := fresh "x2" in
    let H1' := fresh "H1" in
    let H2' := fresh "H2" in
    apply lift_bool_exists in H2;
    destruct H1 as [x1 H1']; destruct H2 as [x2 H2'];
    exists x1, x2
  | H : l = _ -> @ex _ _ |- _ =>
    let x := fresh "x" in
    let H' := fresh "H" in
    apply lift_bool_exists in H;
    destruct H as [x H'];
    exists (func x l)
  | H : @ex _ _ |- _ =>
    let x := fresh "x" in
    let H' := fresh "H" in
    destruct H as [x H'];
    exists (func x r)
  end;
  repeat match goal with
  | H : l = _ -> @ex _ _ |- _ =>
    let x := fresh "x" in
    let H' := fresh "H" in
    apply lift_bool_exists in H;
    destruct H as [x H'];
    exists x
  | H : @ex _ _ |- _ =>
    let x := fresh "x" in
    let H' := fresh "H" in
    destruct H as [x H'];
    exists x
  end;
  (* Attempt to shrink size of problem.
     I originally used just one match here with a non-linear pattern, but it
     appears it matched up to convertability and so definitions could break
     the generalization. *)
  try match goal with
      | _ : l = _ -> ?v = r |- _ => match goal with |- context[v] => generalize dependent v; intros end
      | _ : l = _ -> Bool.eqb ?v r = true |- _ => match goal with |- context[v] => generalize dependent v; intros end
      end;
  unbool_comparisons; unbool_comparisons_goal;
  repeat match goal with
  | _ : context[?li =? ?ri] |- _ =>
    specialize (Z.eqb_eq li ri); generalize dependent (li =? ri); intros
  | |- context[?li =? ?ri] =>
    specialize (Z.eqb_eq li ri); generalize (li =? ri); intros
  end;
  solve_bool_with_Z.

Ltac run_main_solver_impl :=
(* Attempt a simple proof first to avoid lengthy preparation steps (especially
   as the large proof terms can upset subsequent proofs). *)
try solve [default_andor];
constructor;
try simple_omega;
prepare_for_solver;
(*dump_context;*)
unbool_comparisons_goal; (* Applying the ArithFact constructor will reveal an = true, so this might do more than it did in prepare_for_solver *)
repeat match goal with |- and _ _ => split end;
main_solver.

(* This can be redefined to remove the abstract. *)
Ltac run_main_solver :=
  solve
    [ abstract run_main_solver_impl
    | run_main_solver_impl (* for cases where there's an evar in the goal *)
    ].

Ltac is_fixpoint ty :=
  match ty with
  | forall _reclimit, Acc _ _reclimit -> _ => idtac
  | _ -> ?res => is_fixpoint res
  end.

Ltac clear_fixpoints :=
  repeat
    match goal with
    | H:_ -> ?res |- _ => is_fixpoint res; clear H
    end.
Ltac clear_proof_bodies :=
  repeat match goal with
  | H := _ : ?ty |- _ =>
    match type of ty with
    | Prop => clearbody H
    end
  end.

Ltac solve_arithfact :=
  clear_proof_bodies;
  try solve [squashed_andor_solver]; (* Do this first so that it can name the intros *)
  intros; (* To solve implications for derive_m *)
  clear_fixpoints; (* Avoid using recursive calls *)
  cbv beta; (* Goal might be eta-expanded *)
  solve
    [ solve_unknown
    | assumption
    | match goal with |- ArithFact ((?x <=? ?x <=? ?x)) => exact trivial_range end
    | eauto 2 with sail (* the low search bound might not be necessary *)
    | fill_in_evar_eq
    | match goal with |- context [projT1 ?X] => apply (ArithFact_self_proof X) end
    | match goal with |- context [projT1 ?X] => apply (ArithFactP_self_proof X) end
    (* Trying reflexivity will fill in more complex metavariable examples than
       fill_in_evar_eq above, e.g., 8 * n =? 8 * ?Goal3 *)
    | constructor; apply Z.eqb_eq; reflexivity
    | constructor; repeat match goal with |- and _ _ => split end; z_comparisons
    | run_main_solver
    ].

(* Add an indirection so that you can redefine run_solver to fail to get
   slow running constraints into proof mode. *)
Ltac run_solver := solve_arithfact.

Hint Extern 0 (ArithFact _) => run_solver : typeclass_instances.
Hint Extern 0 (ArithFactP _) => run_solver : typeclass_instances.

Hint Unfold length_mword : sail.

Lemma unit_comparison_lemma : true = true <-> True.
intuition.
Qed.
Hint Resolve unit_comparison_lemma : sail.

Definition neq_atom (x : Z) (y : Z) : bool := negb (Z.eqb x y).
Hint Unfold neq_atom : sail.

Lemma ReasonableSize_witness (a : Z) (w : mword a) : ReasonableSize a.
constructor.
destruct a.
* auto with zarith.
* auto using Z.le_ge, Zle_0_pos.
* destruct w.
Qed.

Hint Extern 0 (ReasonableSize ?A) => (unwrap_ArithFacts; solve [apply ReasonableSize_witness; assumption | constructor; auto with zarith]) : typeclass_instances.

Definition to_range (x : Z) : {y : Z & ArithFact ((x <=? y <=? x))} := build_ex x.

Instance mword_Bitvector {a : Z} `{ArithFact (a >=? 0)} : (Bitvector (mword a)) := {
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

(*val string_of_bv : forall a. Bitvector a => a -> string *)
Definition string_of_bv v := show_bitlist (bits_of v).

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
Fixpoint index_list' from to step n :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    match n with
    | O => []
    | S n => from :: index_list' (from + step) to step n
    end
  else [].

Definition index_list from to step :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    index_list' from to step (S (Z.abs_nat (from - to)))
  else [].

Fixpoint foreach_Z' {Vars} from to step n (vars : Vars) (body : Z -> Vars -> Vars) : Vars :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    match n with
    | O => vars
    | S n => let vars := body from vars in foreach_Z' (from + step) to step n vars body
    end
  else vars.

Definition foreach_Z {Vars} from to step vars body :=
  foreach_Z' (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.

(* Define these in proof mode to avoid anomalies related to abstract.
   (See https://github.com/coq/coq/issues/10959) *)

Fixpoint foreach_Z_up' {Vars} (from to step off : Z) (n:nat) `{ArithFact (0 <? step)} `{ArithFact (0 <=? off)} (vars : Vars) (body : forall (z : Z) `(ArithFact ((from <=? z <=? to))), Vars -> Vars) {struct n} : Vars.
refine (
  if sumbool_of_bool (from + off <=? to) then
    match n with
    | O => vars
    | S n => let vars := body (from + off) _ vars in foreach_Z_up' _ from to step (off + step) n _ _ vars body
    end
  else vars
).
Defined.

Fixpoint foreach_Z_down' {Vars} from to step off (n:nat) `{ArithFact (0 <? step)} `{ArithFact (off <=? 0)} (vars : Vars) (body : forall (z : Z) `(ArithFact ((to <=? z <=? from))), Vars -> Vars) {struct n} : Vars.
refine (
  if sumbool_of_bool (to <=? from + off) then
    match n with
    | O => vars
    | S n => let vars := body (from + off) _ vars in foreach_Z_down' _ from to step (off - step) n _ _ vars body
    end
  else vars
).
Defined.

Definition foreach_Z_up {Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_Z_up' (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_Z_down {Vars} from to step vars body `{ArithFact (0 <? step)} :=
    foreach_Z_down' (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

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

Definition ediv_with_eq n m : {o : Z & ArithFact (o =? ZEuclid.div n m)} := build_ex (ZEuclid.div n m).
Definition emod_with_eq n m : {o : Z & ArithFact (o =? ZEuclid.modulo n m)} := build_ex (ZEuclid.modulo n m).
Definition abs_with_eq n   : {o : Z & ArithFact (o =? Z.abs n)} := build_ex (Z.abs n).

(* Similarly, for ranges (currently in MIPS) *)

Definition eq_range {n m o p} (l : {l & ArithFact (n <=? l <=? m)}) (r : {r & ArithFact (o <=? r <=? p)}) : bool :=
  (projT1 l) =? (projT1 r).
Definition add_range {n m o p} (l : {l & ArithFact (n <=? l <=? m)}) (r : {r & ArithFact (o <=? r <=? p)})
  : {x & ArithFact (n+o <=? x <=? m+p)} :=
  build_ex ((projT1 l) + (projT1 r)).
Definition sub_range {n m o p} (l : {l & ArithFact (n <=? l <=? m)}) (r : {r & ArithFact (o <=? r <=? p)})
  : {x & ArithFact (n-p <=? x <=? m-o)} :=
  build_ex ((projT1 l) - (projT1 r)).
Definition negate_range {n m} (l : {l : Z & ArithFact (n <=? l <=? m)})
  : {x : Z & ArithFact ((- m) <=? x <=? (- n))} :=
  build_ex (- (projT1 l)).

Definition min_atom (a : Z) (b : Z) : {c : Z & ArithFact (((c =? a) || (c =? b)) && (c <=? a) && (c <=? b))} :=
  build_ex (Z.min a b).
Definition max_atom (a : Z) (b : Z) : {c : Z & ArithFact (((c =? a) || (c =? b)) && (c >=? a) && (c >=? b))} :=
  build_ex (Z.max a b).


(*** Generic vectors *)

Definition vec (T:Type) (n:Z) := { l : list T & length_list l = n }.
Definition vec_length {T n} (v : vec T n) := n.
Definition vec_access_dec {T n} (v : vec T n) m `{ArithFact ((0 <=? m <? n))} : T :=
  access_list_dec (projT1 v) m.

Definition vec_access_inc {T n} (v : vec T n) m `{ArithFact (0 <=? m <? n)} : T :=
  access_list_inc (projT1 v) m.

Program Definition vec_init {T} (t : T) (n : Z) `{ArithFact (n >=? 0)} : vec T n :=
  existT _ (repeat [t] n) _.
Next Obligation.
intros.
cbv beta.
rewrite repeat_length. 2: apply Z_geb_ge, fact.
unfold length_list.
simpl.
auto with zarith.
Qed.

Definition vec_concat {T m n} (v : vec T m) (w : vec T n) : vec T (m + n).
refine (existT _ (projT1 v ++ projT1 w) _).
destruct v.
destruct w.
simpl.
unfold length_list in *.
rewrite <- e, <- e0.
rewrite app_length.
rewrite Nat2Z.inj_add.
reflexivity.
Defined.

Lemma skipn_length {A n} {l: list A} : (n <= List.length l -> List.length (skipn n l) = List.length l - n)%nat.
revert l.
induction n.
* simpl. auto with arith.
* intros l H.
  destruct l.
  + inversion H.
  + simpl in H.
    simpl.
    rewrite IHn; auto with arith.
Qed.
Lemma update_list_inc_length {T} {l:list T} {m x} : 0 <= m < length_list l -> length_list (update_list_inc l m x) = length_list l.
unfold update_list_inc, list_update, length_list.
intro H.
f_equal.
assert ((0 <= Z.to_nat m < Datatypes.length l)%nat).
{ destruct H as [H1 H2].
  split.
  + change 0%nat with (Z.to_nat 0).
    apply Z2Nat.inj_le; auto with zarith.
  + rewrite <- Nat2Z.id.
    apply Z2Nat.inj_lt; auto with zarith.
}
rewrite app_length.
rewrite firstn_length_le; only 2:lia.
cbn -[skipn].
rewrite skipn_length;
lia.
Qed.

Program Definition vec_update_dec {T n} (v : vec T n) m t `{ArithFact (0 <=? m <? n)} : vec T n := existT _ (update_list_dec (projT1 v) m t) _.
Next Obligation.
intros; cbv beta.
unfold update_list_dec.
rewrite update_list_inc_length.
+ destruct v. apply e.
+ destruct H as [H].
  unbool_comparisons.
  destruct v. simpl (projT1 _). rewrite e.
  lia.
Qed.

Program Definition vec_update_inc {T n} (v : vec T n) m t `{ArithFact (0 <=? m <? n)} : vec T n := existT _ (update_list_inc (projT1 v) m t) _.
Next Obligation.
intros; cbv beta.
rewrite update_list_inc_length.
+ destruct v. apply e.
+ destruct H.
  unbool_comparisons.
  destruct v. simpl (projT1 _). rewrite e.
  auto.
Qed.

Program Definition vec_map {S T} (f : S -> T) {n} (v : vec S n) : vec T n := existT _ (List.map f (projT1 v)) _.
Next Obligation.
destruct v as [l H].
cbn.
unfold length_list.
rewrite map_length.
apply H.
Qed.

Program Definition just_vec {A n} (v : vec (option A) n) : option (vec A n) :=
  match just_list (projT1 v) with
  | None => None
  | Some v' => Some (existT _ v' _)
  end.
Next Obligation.
intros; cbv beta.
rewrite <- (just_list_length_Z _ _ Heq_anonymous).
destruct v.
assumption.
Qed.

Definition list_of_vec {A n} (v : vec A n) : list A := projT1 v.

Definition vec_eq_dec {T n} (D : forall x y : T, {x = y} + {x <> y}) (x y : vec T n) :
  {x = y} + {x <> y}.
refine (if List.list_eq_dec D (projT1 x) (projT1 y) then left _ else right _).
* apply eq_sigT_hprop; auto using ZEqdep.UIP.
* contradict n0. rewrite n0. reflexivity.
Defined.

Instance Decidable_eq_vec {T : Type} {n} `(DT : forall x y : T, Decidable (x = y)) :
  forall x y : vec T n, Decidable (x = y).
refine (fun x y => {|
  Decidable_witness := proj1_sig (bool_of_sumbool (vec_eq_dec (fun x y => generic_dec x y) x y))
|}).
destruct (vec_eq_dec _ x y); simpl; split; congruence.
Defined.

Program Definition vec_of_list {A} n (l : list A) : option (vec A n) :=
  if sumbool_of_bool (n =? length_list l) then Some (existT _ l _) else None.
Next Obligation.
symmetry.
apply Z.eqb_eq.
assumption.
Qed.

Definition vec_of_list_len {A} (l : list A) : vec A (length_list l) := existT _ l (eq_refl _).

Definition map_bind {A B} (f : A -> option B) (a : option A) : option B :=
match a with
| Some a' => f a'
| None => None
end.

Definition sub_nat (x : Z) `{ArithFact (x >=? 0)} (y : Z) `{ArithFact (y >=? 0)} :
  {z : Z & ArithFact (z >=? 0)} :=
  let z := x - y in
  if sumbool_of_bool (z >=? 0) then build_ex z else build_ex 0.

Definition min_nat (x : Z) `{ArithFact (x >=? 0)} (y : Z) `{ArithFact (y >=? 0)} :
  {z : Z & ArithFact (z >=? 0)} :=
  build_ex (Z.min x y).

Definition max_nat (x : Z) `{ArithFact (x >=? 0)} (y : Z) `{ArithFact (y >=? 0)} :
  {z : Z & ArithFact (z >=? 0)} :=
  build_ex (Z.max x y).

Definition shl_int_1 (x y : Z) `{HE:ArithFact (x =? 1)} `{HR:ArithFact (0 <=? y <=? 3)}: {z : Z & ArithFact (member_Z_list z [1;2;4;8])}.
refine (existT _ (shl_int x y) _).
destruct HE as [HE].
destruct HR as [HR].
unbool_comparisons.
assert (y = 0 \/ y = 1 \/ y = 2 \/ y = 3) by lia.
constructor.
intuition (subst; compute; auto).
Defined.

Definition shl_int_8 (x y : Z) `{HE:ArithFact (x =? 8)} `{HR:ArithFact (0 <=? y <=? 3)}: {z : Z & ArithFact (member_Z_list z [8;16;32;64])}.
refine (existT _ (shl_int x y) _).
destruct HE as [HE].
destruct HR as [HR].
unbool_comparisons.
assert (y = 0 \/ y = 1 \/ y = 2 \/ y = 3) by lia.
constructor.
intuition (subst; compute; auto).
Defined.

Definition shl_int_32 (x y : Z) `{HE:ArithFact (x =? 32)} `{HR:ArithFact (member_Z_list y [0;1])}: {z : Z & ArithFact (member_Z_list z [32;64])}.
refine (existT _ (shl_int x y) _).
destruct HE as [HE].
destruct HR as [HR].
constructor.
unbool_comparisons.
destruct HR as [HR | [HR | []]];
subst; compute;
auto.
Defined.

Definition shr_int_32 (x y : Z) `{HE:ArithFact (0 <=? x <=? 31)} `{HR:ArithFact (y =? 1)}: {z : Z & ArithFact (0 <=? z <=? 15)}.
refine (existT _ (shr_int x y) _).
abstract (
  destruct HE as [HE];
  destruct HR as [HR];
  unbool_comparisons;
  subst;
  constructor;
  unbool_comparisons_goal;
  unfold shr_int;
  rewrite <- Z.div2_spec;
  rewrite Z.div2_div;
  specialize (Z.div_mod x 2);
  specialize (Z.mod_pos_bound x 2);
  generalize (Z.div x 2);
  generalize (x mod 2);
  intros;
  nia).
Defined.

Lemma shl_8_ge_0 {n} : shl_int 8 n >= 0.
unfold shl_int.
apply Z.le_ge.  
apply <- Z.shiftl_nonneg.
lia.
Qed.
Hint Resolve shl_8_ge_0 : sail.

(* This is needed because Sail's internal constraint language doesn't have
   < and could disappear if we add it... *)

Lemma sail_lt_ge (x y : Z) :
  x < y <-> y >= x +1.
lia.
Qed.
Hint Resolve sail_lt_ge : sail.
