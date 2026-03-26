open Ast
open BinInt
open Bit
open BitList
open Datatypes
open ListDef
open PeanoNat

val value_of_lit : lit -> value

module Primops :
 sig
  val gt_int : value -> value -> value option

  val lt_int : value -> value -> value option

  val add_int : value -> value -> value option

  val sub_int : value -> value -> value option

  val zero_extend : value -> value -> value option
 end
