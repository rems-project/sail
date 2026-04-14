open BinNat
open BinPos
open Datatypes
open Nat0
open Definitions

module BoolList :
 sig
  val add_lsb : bool -> Big_int_Z.big_int option -> Big_int_Z.big_int option

  val bits_to_N : bool list -> Big_int_Z.big_int option -> Big_int_Z.big_int

  val to_Z_unsigned :
    bool list -> Big_int_Z.big_int option -> Big_int_Z.big_int

  val prefix_size : Big_int_Z.big_int option -> Big_int_Z.big_int

  val to_bv' : bool list -> Big_int_Z.big_int option -> bv

  val to_bv : bool list -> bv
 end
