open AbsBitvector
open BinInt
open BinNat
open Bit
open Datatypes
open Interval
open List0
open ListDef
open Nat0
open PeanoNat
open Specif
open Base
open Countable
open Definitions
open Fin_maps
open Gmap
open List_basics
open Numbers

module B :
 sig
  type bvset = AbsBitvector.Dom.bvset =
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

  val abst : bvn -> bvset

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

module I :
 sig
  type endpoints =
    (Big_int_Z.big_int option * Big_int_Z.big_int option) coq_sig

  type interval = Dom.interval =
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

module Ops :
 sig
  val nonneg_top : I.t

  val unsigned_lo : Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int

  val unsigned_hi : Three.ubit list -> Big_int_Z.big_int -> Big_int_Z.big_int

  val bits_unsigned_interval : Three.ubit list -> I.t

  val unsigned : B.t -> I.t

  val bits_signed_interval : Three.ubit list -> I.t

  val signed : B.t -> I.t

  val zeros_nat : Big_int_Z.big_int -> B.t

  val ones_nat : Big_int_Z.big_int -> B.t

  val nonneg_range :
    I.t -> (Big_int_Z.big_int * Big_int_Z.big_int option) option

  val zeros : Big_int_Z.big_int -> I.t -> B.t

  val ones : Big_int_Z.big_int -> I.t -> B.t

  val count_leading_B0 : Three.ubit list -> Big_int_Z.big_int

  val count_until_B1 : Three.ubit list -> Big_int_Z.big_int

  val bits_clz_interval : Three.ubit list -> I.t

  val count_leading_zeros : B.t -> I.t

  val bits_ctz_interval : Three.ubit list -> I.t

  val count_trailing_zeros : B.t -> I.t

  val zero_extend_one_width : Three.ubit list -> Big_int_Z.big_int -> B.t

  val zero_extend_to_width : B.t -> Big_int_Z.big_int -> B.t

  val zero_extend : Big_int_Z.big_int -> B.t -> I.t -> B.t

  val sign_extend_one_width : Three.ubit list -> Big_int_Z.big_int -> B.t

  val sign_extend_to_width : B.t -> Big_int_Z.big_int -> B.t

  val sign_extend : Big_int_Z.big_int -> B.t -> I.t -> B.t

  val bits_length : B.t -> I.t
 end
