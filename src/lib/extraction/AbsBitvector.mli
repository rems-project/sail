open BinNat
open Bit
open Datatypes
open List0
open ListDef
open Nat0
open OptionUtil
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
open Numbers

module Bits :
 sig
  type t = bvn
 end

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

  val _UU03b1_ : bvn -> bvset

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
 end
