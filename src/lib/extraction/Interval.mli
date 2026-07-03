open BinInt
open Datatypes
open OptionUtil
open Specif
open ZArith_dec
open Base
open Option

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

  val abst : Big_int_Z.big_int -> interval

  val concrete : interval -> Big_int_Z.big_int option

  val compare_endpoints :
    (Big_int_Z.big_int -> Big_int_Z.big_int -> bool) -> Big_int_Z.big_int
    option -> Big_int_Z.big_int option -> bool

  val lt : interval -> interval -> bool option

  val gt : interval -> interval -> bool option

  val lteq : interval -> interval -> bool option

  val gteq : interval -> interval -> bool option

  val negate_endpoints :
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val negate : interval -> interval

  val add_endpoints :
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val add : interval -> interval -> interval

  val sub : interval -> interval -> interval

  val four_corner_endpoints :
    (Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int) ->
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val lift_binop :
    (Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int) -> interval
    -> interval -> interval

  val mult : interval -> interval -> interval

  val max_endpoints :
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val max : interval -> interval -> interval

  val min_endpoints :
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val min : interval -> interval -> interval

  val abs_endpoint :
    (Big_int_Z.big_int option * Big_int_Z.big_int option) ->
    Big_int_Z.big_int option * Big_int_Z.big_int option

  val abs : interval -> interval

  val tdiv : interval -> interval -> interval

  val tmod : interval -> interval -> interval

  val fdiv : interval -> interval -> interval

  val fmod : interval -> interval -> interval

  val ediv : interval -> interval -> interval

  val emod : interval -> interval -> interval
 end
