open BinNat
open BvUtil
open Datatypes
open ListDef
open Definitions

type bit =
| B0
| B1

val bit_to_bool : bit -> bool

module Bits :
 sig
  val to_bvn : bit list -> bvn
 end

module Three :
 sig
  type ubit =
  | B0
  | B1
  | BU

  val from_bool : bool -> ubit

  val bit_not : ubit -> ubit

  val bit_or : ubit -> ubit -> ubit

  val bit_and : ubit -> ubit -> ubit

  val bit_xor : ubit -> ubit -> ubit

  val bit_join : ubit -> ubit -> ubit

  val bit_meet : ubit -> ubit -> ubit option

  val bit_leb : ubit -> ubit -> bool
 end
