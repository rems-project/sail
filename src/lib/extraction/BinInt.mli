open BinNat
open BinPos
open Bool
open Datatypes
open DecidableClass
open Decimal
open Hexadecimal
open NatDef
open Number
open PosDef

type __ = Obj.t

module Z :
 sig
  val double : Big_int_Z.big_int -> Big_int_Z.big_int

  val succ_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred_double : Big_int_Z.big_int -> Big_int_Z.big_int

  val pos_sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val add : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val opp : Big_int_Z.big_int -> Big_int_Z.big_int

  val sub : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val mul : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val pow_pos : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val pow : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val compare : Big_int_Z.big_int -> Big_int_Z.big_int -> comparison

  val leb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ltb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val eqb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val max : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val min : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val to_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_N : Big_int_Z.big_int -> Big_int_Z.big_int

  val to_pos : Big_int_Z.big_int -> Big_int_Z.big_int

  val pos_div_eucl :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * Big_int_Z.big_int

  val div_eucl :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * Big_int_Z.big_int

  val div : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val modulo : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val quotrem :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * Big_int_Z.big_int

  val quot : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val rem : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val even : Big_int_Z.big_int -> bool

  val div2 : Big_int_Z.big_int -> Big_int_Z.big_int

  val sqrtrem : Big_int_Z.big_int -> Big_int_Z.big_int * Big_int_Z.big_int

  val shiftl : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val shiftr : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_lor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_land : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val coq_lxor : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  type t = Big_int_Z.big_int

  val zero : Big_int_Z.big_int

  val one : Big_int_Z.big_int

  val two : Big_int_Z.big_int

  val succ : Big_int_Z.big_int -> Big_int_Z.big_int

  val pred : Big_int_Z.big_int -> Big_int_Z.big_int

  val square : Big_int_Z.big_int -> Big_int_Z.big_int

  val sgn : Big_int_Z.big_int -> Big_int_Z.big_int

  val geb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val gtb : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val abs : Big_int_Z.big_int -> Big_int_Z.big_int

  val abs_nat : Big_int_Z.big_int -> Big_int_Z.big_int

  val abs_N : Big_int_Z.big_int -> Big_int_Z.big_int

  val to_N : Big_int_Z.big_int -> Big_int_Z.big_int

  val of_uint : Decimal.uint -> Big_int_Z.big_int

  val of_hex_uint : Hexadecimal.uint -> Big_int_Z.big_int

  val of_num_uint : uint -> Big_int_Z.big_int

  val of_int : Decimal.signed_int -> Big_int_Z.big_int

  val of_hex_int : Hexadecimal.signed_int -> Big_int_Z.big_int

  val of_num_int : signed_int -> Big_int_Z.big_int

  val to_int : Big_int_Z.big_int -> Decimal.signed_int

  val to_hex_int : Big_int_Z.big_int -> Hexadecimal.signed_int

  val to_num_int : Big_int_Z.big_int -> signed_int

  val to_num_hex_int : Big_int_Z.big_int -> signed_int

  val iter : Big_int_Z.big_int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val odd : Big_int_Z.big_int -> bool

  val quot2 : Big_int_Z.big_int -> Big_int_Z.big_int

  val log2 : Big_int_Z.big_int -> Big_int_Z.big_int

  val sqrt : Big_int_Z.big_int -> Big_int_Z.big_int

  val gcd : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val ggcd :
    Big_int_Z.big_int -> Big_int_Z.big_int ->
    Big_int_Z.big_int * (Big_int_Z.big_int * Big_int_Z.big_int)

  val testbit : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val ldiff : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val eq_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  module Private_BootStrap :
   sig
   end

  val coq_Decidable_eq_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable

  val coq_Decidable_lt_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable

  val coq_Decidable_le_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable

  val coq_Decidable_gt_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable

  val coq_Decidable_ge_Z :
    Big_int_Z.big_int -> Big_int_Z.big_int -> coq_Decidable

  val leb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect

  val ltb_spec0 : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  val measure_right_induction :
    ('a1 -> Big_int_Z.big_int) -> Big_int_Z.big_int -> ('a1 -> __ -> ('a1 ->
    __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

  val measure_left_induction :
    ('a1 -> Big_int_Z.big_int) -> Big_int_Z.big_int -> ('a1 -> __ -> ('a1 ->
    __ -> 'a2) -> 'a2) -> 'a1 -> 'a2

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1

    val max_case :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

    val min_case_strong :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) ->
      'a1

    val min_case :
      Big_int_Z.big_int -> Big_int_Z.big_int -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool
   end

  val max_case_strong :
    Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) ->
    'a1

  val max_case : Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1

  val max_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val min_case_strong :
    Big_int_Z.big_int -> Big_int_Z.big_int -> (__ -> 'a1) -> (__ -> 'a1) ->
    'a1

  val min_case : Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 -> 'a1 -> 'a1

  val min_dec : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val sqrt_up : Big_int_Z.big_int -> Big_int_Z.big_int

  val log2_up : Big_int_Z.big_int -> Big_int_Z.big_int

  module Private_NZDiv :
   sig
   end

  module Private_Div :
   sig
    module Quot2Div :
     sig
      val div : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

      val modulo : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int
     end

    module NZQuot :
     sig
     end
   end

  val lcm : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val eqb_spec : Big_int_Z.big_int -> Big_int_Z.big_int -> reflect

  val b2z : bool -> Big_int_Z.big_int

  val setbit : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val clearbit : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int

  val lnot : Big_int_Z.big_int -> Big_int_Z.big_int

  val ones : Big_int_Z.big_int -> Big_int_Z.big_int
 end
