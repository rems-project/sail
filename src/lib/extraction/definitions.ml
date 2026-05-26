open BinInt
open Base
open List_monad
open List_numbers
open Numbers

(** val bv_modulus : Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_modulus n =
  Z.pow (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) (Z.of_N n)

(** val bv_wrap :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_wrap n z =
  Z.modulo z (bv_modulus n)

type bv = { bv_unsigned : Big_int_Z.big_int }

(** val coq_Z_to_bv : Big_int_Z.big_int -> Big_int_Z.big_int -> bv **)

let coq_Z_to_bv n z =
  { bv_unsigned = (bv_wrap n z) }

(** val bv_to_bits : Big_int_Z.big_int -> bv -> bool list **)

let bv_to_bits n b =
  fmap (Obj.magic (fun _ _ -> List_monad.Coq_list.list_fmap)) (fun i ->
    Z.testbit b.bv_unsigned i)
    (Obj.magic Coq_list.seqZ Big_int_Z.zero_big_int (Z.of_N n))

type bvn = { bvn_n : Big_int_Z.big_int; bvn_val : bv }

(** val bvn_to_bv : Big_int_Z.big_int -> bvn -> bv option **)

let bvn_to_bv n b =
  if decide (decide_rel N.eq_dec b.bvn_n n) then Some b.bvn_val else None
