open Datatypes
open Nat0

module Pos :
 sig
  val succ : Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_N : Big_int_Z.big_int -> Big_int_Z.big_int

  type mask =
  | IsNul
  | IsPos of Big_int_Z.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big_int_Z.big_int -> mask

  val sub_mask : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val sub_mask_carry : Big_int_Z.big_int -> Big_int_Z.big_int -> mask

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val iter : ('a1 -> 'a1) -> 'a1 -> Big_int_Z.big_int -> 'a1

  val div2 : Big_int_Z.big_int -> Big_int_Z.big_int

  val div2_up : Big_int_Z.big_int -> Big_int_Z.big_int

  val compare_cont :
    comparison -> Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val sqrtrem_step :
    (Big_int_Z.big_int -> Big_int_Z.big_int) -> (Big_int_Z.big_int ->
    Big_int_Z.big_int) -> (Big_int_Z.big_int * mask) ->
    Big_int_Z.big_int * mask

  val sqrtrem : Big_int_Z.big_int -> Big_int_Z.big_int * mask

  val coq_Nsucc_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_Ndouble : Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_lor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_land : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_lxor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big_int_Z.big_int -> 'a1 -> 'a1

  val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_succ_nat : Big_int_Z.big_int -> Big_int_Z.big_int
 end
