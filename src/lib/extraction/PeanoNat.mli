
module Nat :
 sig
  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
 end
