open Ast
open BinInt
open Bit
open BitList
open Bool
open Datatypes
open IdUtil
open ListDef
open ListUtil
open PeanoNat
open QArith_base

val value_of_lit : lit -> value

val value_cmp : (value -> bool) -> value -> value -> bool

val is_unknown : value -> bool

val value_eqb : value -> value -> bool

module Primops :
 sig
  val gt_int : value -> value -> value option

  val lt_int : value -> value -> value option

  val add_int : value -> value -> value option

  val sub_int : value -> value -> value option

  val zero_extend : value -> value -> value option
 end
