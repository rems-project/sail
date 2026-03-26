open Bit
open Datatypes
open List0
open ListDef
open OptionUtil
open Specif
open Base
open Countable
open Fin_maps
open Gmap
open Numbers

module BitList :
 sig
  type t = bit list
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

  val _UU03b1_ : bit list -> t
 end
