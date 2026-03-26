open BinInt
open Datatypes
open OptionUtil
open Specif
open ZArith_dec

module Dom :
 sig
  type endpoints =
    (Big_int_Z.big_int option * Big_int_Z.big_int option) coq_sig

  type interval =
  | Empty
  | Ends of endpoints

  val interval_rect : 'a1 -> (endpoints -> 'a1) -> interval -> 'a1

  val interval_rec : 'a1 -> (endpoints -> 'a1) -> interval -> 'a1

  type t = interval

  val low : endpoints -> Big_int_Z.big_int option

  val high : endpoints -> Big_int_Z.big_int option

  val extend :
    (Big_int_Z.big_int -> Big_int_Z.big_int -> bool) -> Big_int_Z.big_int
    option -> Big_int_Z.big_int option -> Big_int_Z.big_int option

  val join : interval -> interval -> interval

  val meet : interval -> interval -> interval

  val bot : interval

  val top : interval

  val low_leb : Big_int_Z.big_int option -> Big_int_Z.big_int option -> bool

  val high_leb : Big_int_Z.big_int option -> Big_int_Z.big_int option -> bool

  val leb : interval -> interval -> bool

  val _UU03b1_ : Big_int_Z.big_int -> interval
 end
