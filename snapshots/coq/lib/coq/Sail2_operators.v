Require Import Sail2_values.
Require List.
Import List.ListNotations.

(*** Bit vector operations *)

Section Bitvectors.
Context {a b c} `{Bitvector a} `{Bitvector b} `{Bitvector c}.

(*val concat_bv : forall 'a 'b 'c. Bitvector 'a, Bitvector 'b, Bitvector 'c => 'a -> 'b -> 'c*)
Definition concat_bv (l : a) (r : b) : list bitU := bits_of l ++ bits_of r.

(*val cons_bv : forall 'a 'b 'c. Bitvector 'a, Bitvector 'b => bitU -> 'a -> 'b*)
Definition cons_bv b' (v : a) : list bitU := b' :: bits_of v.

Definition cast_unit_bv b : list bitU := [b].
Definition bv_of_bit len b : list bitU := extz_bits len [b].

(*Definition most_significant v := match bits_of v with
  | cons b _ => b
  | _ => failwith "most_significant applied to empty vector"
  end.

Definition get_max_representable_in sign (n : integer) : integer :=
  if (n = 64) then match sign with | true -> max_64 | false -> max_64u end
  else if (n=32) then match sign with | true -> max_32 | false -> max_32u end
  else if (n=8) then max_8
  else if (n=5) then max_5
  else match sign with | true -> integerPow 2 ((natFromInteger n) -1)
                       | false -> integerPow 2 (natFromInteger n)
       end

Definition get_min_representable_in _ (n : integer) : integer :=
  if n = 64 then min_64
  else if n = 32 then min_32
  else if n = 8 then min_8
  else if n = 5 then min_5
  else 0 - (integerPow 2 (natFromInteger n))

val arith_op_bv_int : forall 'a 'b. Bitvector 'a =>
  (integer -> integer -> integer) -> bool -> 'a -> integer -> 'a*)
Definition arith_op_bv_int {a} `{Bitvector a} (op : Z -> Z -> Z) (sign : bool) (l : a) (r : Z) : a :=
  let r' := of_int (length l) r in
  arith_op_bv op sign l r'.

(*val arith_op_int_bv : forall 'a 'b. Bitvector 'a =>
  (integer -> integer -> integer) -> bool -> integer -> 'a -> 'a*)
Definition arith_op_int_bv {a} `{Bitvector a} (op : Z -> Z -> Z) (sign : bool) (l : Z) (r : a) : a :=
  let l' := of_int (length r) l in
  arith_op_bv op sign l' r.
(*
Definition add_bv_int := arith_op_bv_int Zplus false 1.
Definition sadd_bv_int := arith_op_bv_int Zplus true 1.
Definition sub_bv_int := arith_op_bv_int Zminus false 1.
Definition mult_bv_int := arith_op_bv_int Zmult false 2.
Definition smult_bv_int := arith_op_bv_int Zmult true 2.

(*val arith_op_int_bv : forall 'a 'b. Bitvector 'a, Bitvector 'b =>
  (integer -> integer -> integer) -> bool -> integer -> integer -> 'a -> 'b
Definition arith_op_int_bv op sign size l r :=
  let r' = int_of_bv sign r in
  let n = op l r' in
  of_int (size * length r) n

Definition add_int_bv = arith_op_int_bv integerAdd false 1
Definition sadd_int_bv = arith_op_int_bv integerAdd true 1
Definition sub_int_bv = arith_op_int_bv integerMinus false 1
Definition mult_int_bv = arith_op_int_bv integerMult false 2
Definition smult_int_bv = arith_op_int_bv integerMult true 2

Definition arith_op_bv_bit op sign (size : integer) l r :=
  let l' = int_of_bv sign l in
  let n = op l' (match r with | B1 -> (1 : integer) | _ -> 0 end) in
  of_int (size * length l) n

Definition add_bv_bit := arith_op_bv_bit integerAdd false 1
Definition sadd_bv_bit := arith_op_bv_bit integerAdd true 1
Definition sub_bv_bit := arith_op_bv_bit integerMinus true 1

val arith_op_overflow_bv : forall 'a 'b. Bitvector 'a, Bitvector 'b =>
  (integer -> integer -> integer) -> bool -> integer -> 'a -> 'a -> ('b * bitU * bitU)
Definition arith_op_overflow_bv op sign size l r :=
  let len := length l in
  let act_size := len * size in
  let (l_sign,r_sign) := (int_of_bv sign l,int_of_bv sign r) in
  let (l_unsign,r_unsign) := (int_of_bv false l,int_of_bv false r) in
  let n := op l_sign r_sign in
  let n_unsign := op l_unsign r_unsign in
  let correct_size := of_int act_size n in
  let one_more_size_u := bits_of_int (act_size + 1) n_unsign in
  let overflow :=
    if n <= get_max_representable_in sign len &&
         n >= get_min_representable_in sign len
    then B0 else B1 in
  let c_out := most_significant one_more_size_u in
  (correct_size,overflow,c_out)

Definition add_overflow_bv := arith_op_overflow_bv integerAdd false 1
Definition add_overflow_bv_signed := arith_op_overflow_bv integerAdd true 1
Definition sub_overflow_bv := arith_op_overflow_bv integerMinus false 1
Definition sub_overflow_bv_signed := arith_op_overflow_bv integerMinus true 1
Definition mult_overflow_bv := arith_op_overflow_bv integerMult false 2
Definition mult_overflow_bv_signed := arith_op_overflow_bv integerMult true 2

val arith_op_overflow_bv_bit : forall 'a 'b. Bitvector 'a, Bitvector 'b =>
  (integer -> integer -> integer) -> bool -> integer -> 'a -> bitU -> ('b * bitU * bitU)
Definition arith_op_overflow_bv_bit op sign size l r_bit :=
  let act_size := length l * size in
  let l' := int_of_bv sign l in
  let l_u := int_of_bv false l in
  let (n,nu,changed) := match r_bit with
    | B1 -> (op l' 1, op l_u 1, true)
    | B0 -> (l',l_u,false)
    | BU -> failwith "arith_op_overflow_bv_bit applied to undefined bit"
    end in
  let correct_size := of_int act_size n in
  let one_larger := bits_of_int (act_size + 1) nu in
  let overflow :=
    if changed
    then
      if n <= get_max_representable_in sign act_size && n >= get_min_representable_in sign act_size
      then B0 else B1
    else B0 in
  (correct_size,overflow,most_significant one_larger)

Definition add_overflow_bv_bit := arith_op_overflow_bv_bit integerAdd false 1
Definition add_overflow_bv_bit_signed := arith_op_overflow_bv_bit integerAdd true 1
Definition sub_overflow_bv_bit := arith_op_overflow_bv_bit integerMinus false 1
Definition sub_overflow_bv_bit_signed := arith_op_overflow_bv_bit integerMinus true 1

type shift := LL_shift | RR_shift | RR_shift_arith | LL_rot | RR_rot

val shift_op_bv : forall 'a. Bitvector 'a => shift -> 'a -> integer -> 'a
Definition shift_op_bv op v n :=
  match op with
  | LL_shift ->
     of_bits (get_bits true v n (length v - 1) ++ repeat [B0] n)
  | RR_shift ->
     of_bits (repeat [B0] n ++ get_bits true v 0 (length v - n - 1))
  | RR_shift_arith ->
     of_bits (repeat [most_significant v] n ++ get_bits true v 0 (length v - n - 1))
  | LL_rot ->
     of_bits (get_bits true v n (length v - 1) ++ get_bits true v 0 (n - 1))
  | RR_rot ->
     of_bits (get_bits false v 0 (n - 1) ++ get_bits false v n (length v - 1))
  end

Definition shiftl_bv := shift_op_bv LL_shift (*"<<"*)
Definition shiftr_bv := shift_op_bv RR_shift (*">>"*)
Definition arith_shiftr_bv := shift_op_bv RR_shift_arith
Definition rotl_bv := shift_op_bv LL_rot (*"<<<"*)
Definition rotr_bv := shift_op_bv LL_rot (*">>>"*)

Definition shiftl_mword w n := Machine_word.shiftLeft w (natFromInteger n)
Definition shiftr_mword w n := Machine_word.shiftRight w (natFromInteger n)
Definition rotl_mword w n := Machine_word.rotateLeft (natFromInteger n) w
Definition rotr_mword w n := Machine_word.rotateRight (natFromInteger n) w

Definition rec arith_op_no0 (op : integer -> integer -> integer) l r :=
  if r = 0
  then Nothing
  else Just (op l r)

val arith_op_bv_no0 : forall 'a 'b. Bitvector 'a, Bitvector 'b =>
  (integer -> integer -> integer) -> bool -> integer -> 'a -> 'a -> 'b
Definition arith_op_bv_no0 op sign size l r :=
  let act_size := length l * size in
  let (l',r') := (int_of_bv sign l,int_of_bv sign r) in
  let n := arith_op_no0 op l' r' in
  let (representable,n') :=
    match n with
    | Just n' ->
      (n' <= get_max_representable_in sign act_size &&
         n' >= get_min_representable_in sign act_size, n')
    | _ -> (false,0)
    end in
  if representable then (of_int act_size n') else (of_bits (repeat [BU] act_size))

Definition mod_bv := arith_op_bv_no0 hardware_mod false 1
Definition quot_bv := arith_op_bv_no0 hardware_quot false 1
Definition quot_bv_signed := arith_op_bv_no0 hardware_quot true 1

Definition mod_mword := Machine_word.modulo
Definition quot_mword := Machine_word.unsignedDivide
Definition quot_mword_signed := Machine_word.signedDivide

Definition arith_op_bv_int_no0 op sign size l r :=
  arith_op_bv_no0 op sign size l (of_int (length l) r)

Definition quot_bv_int := arith_op_bv_int_no0 hardware_quot false 1
Definition mod_bv_int := arith_op_bv_int_no0 hardware_mod false 1
*)
Definition replicate_bits_bv {a b} `{Bitvector a} `{Bitvector b} (v : a) count : b := of_bits (repeat (bits_of v) count).
Import List.
Import ListNotations.
Definition duplicate_bit_bv {a} `{Bitvector a} bit len : a := replicate_bits_bv [bit] len.

(*val eq_bv : forall 'a. Bitvector 'a => 'a -> 'a -> bool*)
Definition eq_bv {A} `{Bitvector A} (l : A) r := (unsigned l =? unsigned r).

(*val neq_bv : forall 'a. Bitvector 'a => 'a -> 'a -> bool*)
Definition neq_bv (l : a) (r :a) : bool := (negb (unsigned l =? unsigned r)).
(*
val ucmp_bv : forall 'a. Bitvector 'a => (integer -> integer -> bool) -> 'a -> 'a -> bool
Definition ucmp_bv cmp l r := cmp (unsigned l) (unsigned r)

val scmp_bv : forall 'a. Bitvector 'a => (integer -> integer -> bool) -> 'a -> 'a -> bool
Definition scmp_bv cmp l r := cmp (signed l) (signed r)

Definition ult_bv := ucmp_bv (<)
Definition slt_bv := scmp_bv (<)
Definition ugt_bv := ucmp_bv (>)
Definition sgt_bv := scmp_bv (>)
Definition ulteq_bv := ucmp_bv (<=)
Definition slteq_bv := scmp_bv (<=)
Definition ugteq_bv := ucmp_bv (>=)
Definition sgteq_bv := scmp_bv (>=)
*)

(*val get_slice_int_bv : forall 'a. Bitvector 'a => integer -> integer -> integer -> 'a*)*)
Definition get_slice_int_bv {a} `{Bitvector a} len n lo : a :=
  let hi := lo + len - 1 in
  let bs := bools_of_int (hi + 1) n in
  of_bools (subrange_list false bs hi lo).

(*val set_slice_int_bv : forall 'a. Bitvector 'a => integer -> integer -> integer -> 'a -> integer
Definition set_slice_int_bv {a} `{Bitvector a} len n lo (v : a) :=
  let hi := lo + len - 1 in
  let bs := bits_of_int (hi + 1) n in
  maybe_failwith (signed_of_bits (update_subrange_list false bs hi lo (bits_of v))).*)

End Bitvectors.
