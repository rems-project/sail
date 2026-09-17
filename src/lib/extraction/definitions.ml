open BinInt
open Base
open List_monad
open List_numbers
open Numbers

(** val bv_modulus : Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_modulus n =
  Z.pow (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int) (Z.of_N n)

(** val bv_half_modulus : Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_half_modulus n =
  Z.div (bv_modulus n) (Big_int_Z.mult_int_big_int 2 Big_int_Z.unit_big_int)

(** val bv_wrap :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_wrap n z =
  Z.modulo z (bv_modulus n)

(** val bv_swrap :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int **)

let bv_swrap n z =
  Z.sub (bv_wrap n (Z.add z (bv_half_modulus n))) (bv_half_modulus n)

type bv = { bv_unsigned : Big_int_Z.big_int }

(** val bv_signed : Big_int_Z.big_int -> bv -> Big_int_Z.big_int **)

let bv_signed n b =
  bv_swrap n b.bv_unsigned

(** val coq_Z_to_bv : Big_int_Z.big_int -> Big_int_Z.big_int -> bv **)

let coq_Z_to_bv n z =
  { bv_unsigned = (bv_wrap n z) }

(** val bv_0 : Big_int_Z.big_int -> bv **)

let bv_0 _ =
  { bv_unsigned = Big_int_Z.zero_big_int }

(** val bv_add : Big_int_Z.big_int -> bv -> bv -> bv **)

let bv_add n x y =
  coq_Z_to_bv n (Z.add x.bv_unsigned y.bv_unsigned)

(** val bv_sub : Big_int_Z.big_int -> bv -> bv -> bv **)

let bv_sub n x y =
  coq_Z_to_bv n (Z.sub x.bv_unsigned y.bv_unsigned)

(** val bv_or : Big_int_Z.big_int -> bv -> bv -> bv **)

let bv_or _ x y =
  { bv_unsigned = (Z.coq_lor x.bv_unsigned y.bv_unsigned) }

(** val bv_and : Big_int_Z.big_int -> bv -> bv -> bv **)

let bv_and _ x y =
  { bv_unsigned = (Z.coq_land x.bv_unsigned y.bv_unsigned) }

(** val bv_xor : Big_int_Z.big_int -> bv -> bv -> bv **)

let bv_xor _ x y =
  { bv_unsigned = (Z.coq_lxor x.bv_unsigned y.bv_unsigned) }

(** val bv_not : Big_int_Z.big_int -> bv -> bv **)

let bv_not n x =
  coq_Z_to_bv n (Z.lnot x.bv_unsigned)

(** val bv_zero_extend :
    Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv **)

let bv_zero_extend _ z b =
  coq_Z_to_bv z b.bv_unsigned

(** val bv_sign_extend :
    Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv **)

let bv_sign_extend n z b =
  coq_Z_to_bv z (bv_signed n b)

(** val bv_extract :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv **)

let bv_extract _ s l b =
  coq_Z_to_bv l (Z.shiftr b.bv_unsigned (Z.of_N s))

(** val bv_concat :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv
    -> bv **)

let bv_concat n _ n2 b1 b2 =
  coq_Z_to_bv n
    (Z.coq_lor (Z.shiftl b1.bv_unsigned (Z.of_N n2)) b2.bv_unsigned)

(** val bv_add_Z : Big_int_Z.big_int -> bv -> Big_int_Z.big_int -> bv **)

let bv_add_Z n x y =
  coq_Z_to_bv n (Z.add x.bv_unsigned y)

(** val bv_sub_Z : Big_int_Z.big_int -> bv -> Big_int_Z.big_int -> bv **)

let bv_sub_Z n x y =
  coq_Z_to_bv n (Z.sub x.bv_unsigned y)

(** val bv_to_bits : Big_int_Z.big_int -> bv -> bool list **)

let bv_to_bits n b =
  fmap (Obj.magic (fun _ _ -> List_monad.Coq_list.list_fmap)) (fun i ->
    Z.testbit b.bv_unsigned i)
    (Obj.magic Coq_list.seqZ Big_int_Z.zero_big_int (Z.of_N n))

type bvn = { bvn_n : Big_int_Z.big_int; bvn_val : bv }

(** val bvn_to_bv : Big_int_Z.big_int -> bvn -> bv option **)

let bvn_to_bv n b =
  if decide (decide_rel N.eq_dec b.bvn_n n) then Some b.bvn_val else None
