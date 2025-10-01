open Datatypes
open PosDef

module Z :
 sig
  val double : Big_int_Z.big_int -> Big_int_Z.big_int

  val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pos_sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val opp : Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val gtb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
 end
