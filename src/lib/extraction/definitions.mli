open BinInt
open Base
open List_monad
open List_numbers
open Numbers

val bv_modulus : Big_int_Z.big_int -> Big_int_Z.big_int

val bv_half_modulus : Big_int_Z.big_int -> Big_int_Z.big_int

val bv_wrap : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

val bv_swrap : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

type bv = { bv_unsigned : Big_int_Z.big_int }

val bv_signed : Big_int_Z.big_int -> bv -> Big_int_Z.big_int

val coq_Z_to_bv : Big_int_Z.big_int -> Big_int_Z.big_int -> bv

val bv_0 : Big_int_Z.big_int -> bv

val bv_add : Big_int_Z.big_int -> bv -> bv -> bv

val bv_sub : Big_int_Z.big_int -> bv -> bv -> bv

val bv_or : Big_int_Z.big_int -> bv -> bv -> bv

val bv_and : Big_int_Z.big_int -> bv -> bv -> bv

val bv_xor : Big_int_Z.big_int -> bv -> bv -> bv

val bv_not : Big_int_Z.big_int -> bv -> bv

val bv_zero_extend : Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv

val bv_sign_extend : Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv

val bv_extract :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv

val bv_concat :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bv -> bv ->
  bv

val bv_add_Z : Big_int_Z.big_int -> bv -> Big_int_Z.big_int -> bv

val bv_sub_Z : Big_int_Z.big_int -> bv -> Big_int_Z.big_int -> bv

val bv_to_bits : Big_int_Z.big_int -> bv -> bool list

type bvn = { bvn_n : Big_int_Z.big_int; bvn_val : bv }

val bvn_to_bv : Big_int_Z.big_int -> bvn -> bv option
