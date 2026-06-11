open BinInt
open Definitions

module type CONCRETE =
 sig
  type t
 end

module DomainProperties =
 functor (C:CONCRETE) ->
 functor (D:sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : C.t -> t
 end) ->
 struct
 end

module type SAIL_INT =
 sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : Z.t -> t

  val lt : t -> t -> bool option

  val gt : t -> t -> bool option

  val lteq : t -> t -> bool option

  val gteq : t -> t -> bool option

  val negate : t -> t

  val add : t -> t -> t

  val sub : t -> t -> t

  val mult : t -> t -> t

  val max : t -> t -> t

  val min : t -> t -> t

  val abs : t -> t

  val tdiv : t -> t -> t

  val tmod : t -> t -> t

  val fdiv : t -> t -> t

  val fmod : t -> t -> t

  val ediv : t -> t -> t

  val emod : t -> t -> t

  val concrete : t -> Big_int_Z.big_int option
 end

module Bits =
 struct
  type t = bvn
 end

module type SAIL_BITS =
 sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val _UU03b1_ : Bits.t -> t

  val unknown_bit : t

  val zwbv : t

  val not : t -> t

  val add : t -> t -> t

  val negate : t -> t

  val sub : t -> t -> t

  val coq_and : t -> t -> t

  val coq_or : t -> t -> t

  val xor : t -> t -> t

  val append : t -> t -> t

  val slice : t -> Big_int_Z.big_int -> Big_int_Z.big_int -> t
 end
