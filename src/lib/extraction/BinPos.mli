open Datatypes
open Decimal
open Hexadecimal
open Nat0
open PosDef

module Pos :
 sig
  val succ : Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_N : Big_int_Z.big_int -> Big_int_Z.big_int

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big_int_Z.big_int -> mask

  val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val iter : ('a1 -> 'a1) -> 'a1 -> Big_int_Z.big_int -> 'a1

  val div2 : Big_int_Z.big_int -> Big_int_Z.big_int

  val compare_cont :
    comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val sqrtrem_step :
    (Big_int_Z.big_int -> Big_int_Z.big_int) -> (Big_int_Z.big_int ->
    Big_int_Z.big_int) -> (Big_int_Z.big_int * mask) ->
    Big_int_Z.big_int * mask

  val sqrtrem : Big_int_Z.big_int -> Big_int_Z.big_int * mask

  val sqrt : Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_Nsucc_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_Ndouble : Big_int_Z.big_int -> Big_int_Z.big_int

  val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1

  val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred : Big_int_Z.big_int -> Big_int_Z.big_int

  val square : Big_int_Z.big_int -> Big_int_Z.big_int

  val size_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val size : Big_int_Z.big_int -> Big_int_Z.big_int

  val gcdn :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int

  val gcd : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val ggcdn :
    Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int)

  val ggcd :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int)

  val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val of_uint_acc : Decimal.uint -> Big_int_Z.big_int -> Big_int_Z.big_int

  val of_uint : Decimal.uint -> Big_int_Z.big_int

  val of_hex_uint_acc : uint -> Big_int_Z.big_int -> Big_int_Z.big_int

  val of_hex_uint : uint -> Big_int_Z.big_int

  val to_little_uint : Big_int_Z.big_int -> Decimal.uint

  val to_uint : Big_int_Z.big_int -> Decimal.uint

  val to_little_hex_uint : Big_int_Z.big_int -> uint

  val to_hex_uint : Big_int_Z.big_int -> uint

  val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
 end
