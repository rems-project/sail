open Datatypes
open PosDef

module N :
 sig
  val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val double : Big_int_Z.big_int -> Big_int_Z.big_int

  val succ_pos : Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val pos_div_eucl :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * Big_int_Z.big_int

  val coq_lor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_land : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_lxor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
 end
