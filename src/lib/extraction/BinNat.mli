open Datatypes

module N :
 sig
  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end
