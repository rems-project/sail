open BinPos
open Datatypes
open PosDef

module N :
 sig
  val succ_pos : Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val coq_lor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_land : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
 end
