open BinNat
open Bit
open Datatypes
open List0
open ListDef
open Nat0
open OptionUtil
open PeanoNat
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
open List_basics
open Numbers

module Dom :
 sig
  type bvset =
  | Top
  | Bvs of (Big_int_Z.big_int, Three.ubit list) gmap coq_sig

  val bvset_rect :
    'a1 -> ((Big_int_Z.big_int, Three.ubit list) gmap coq_sig -> 'a1) ->
    bvset -> 'a1

  val bvset_rec :
    'a1 -> ((Big_int_Z.big_int, Three.ubit list) gmap coq_sig -> 'a1) ->
    bvset -> 'a1

  val to_bv_list : bvset -> Three.ubit list list option

  type t = bvset

  val top : bvset

  val bot : t

  val join_aux :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap

  val join : t -> t -> t

  val meet_aux :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap

  val meet : t -> t -> t

  val leb_aux :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> bool

  val leb : t -> t -> bool

  val unknown_bit : bvset

  val zwbv : bvset

  val _UU03b1_ : bvn -> bvset

  val alpha : bvn -> bvset

  val lift_bitwise_gmap :
    (Three.ubit -> Three.ubit -> Three.ubit) -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap ->
    (Big_int_Z.big_int, Three.ubit list) gmap

  val lift_bitwise :
    (Three.ubit -> Three.ubit -> Three.ubit) -> bvset -> bvset -> bvset

  val coq_and : bvset -> bvset -> bvset

  val coq_or : bvset -> bvset -> bvset

  val xor : bvset -> bvset -> bvset

  val not_gmap :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap

  val not : bvset -> bvset

  val add_gmap :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap

  val add : bvset -> bvset -> bvset

  val append_insert :
    Three.ubit list -> Three.ubit list option -> Three.ubit list option

  val append_gmap :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap -> (Big_int_Z.big_int, Three.ubit list) gmap

  val append : bvset -> bvset -> bvset

  val one_bits : Big_int_Z.big_int -> Three.ubit list

  val negate_gmap :
    (Big_int_Z.big_int, Three.ubit list) gmap -> (Big_int_Z.big_int,
    Three.ubit list) gmap

  val negate : bvset -> bvset

  val sub : bvset -> bvset -> bvset

  val slice_bits :
    Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int -> Three.ubit
    list

  val slice_gmap :
    (Big_int_Z.big_int, Three.ubit list) gmap -> Big_int_Z.big_int ->
    Big_int_Z.big_int -> (Big_int_Z.big_int, Three.ubit list) gmap

  val slice : bvset -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvset
 end
