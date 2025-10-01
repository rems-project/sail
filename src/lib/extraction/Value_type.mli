open BinInt
open Datatypes
open ListDef
open Nat0

type bit =
| B0
| B1

type value =
| V_bitvector of bit list
| V_vector of value list
| V_list of value list
| V_int of Big_int_Z.big_int
| V_real of Rational.t
| V_bool of bool
| V_tuple of value list
| V_unit
| V_string of string
| V_ref of string
| V_member of string
| V_ctor of string * value list
| V_record of (string * value) list
| V_attempted_read of string

module Primops :
 sig
  val gt_int : value -> value -> value option

  val lt_int : value -> value -> value option

  val add_int : value -> value -> value option

  val sub_int : value -> value -> value option

  val zero_extend : value -> value -> value option
 end
