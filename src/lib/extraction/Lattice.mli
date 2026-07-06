open Assignment
open Ast
open BinInt
open PatternMatch
open TypeAnnot
open Definitions

module type CONCRETE =
 sig
  type t
 end

module type DOMAIN =
 functor (C:CONCRETE) ->
 sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val abst : C.t -> t
 end

module DomainProperties :
 functor (C:CONCRETE) ->
 functor (D:sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val abst : C.t -> t
 end) ->
 sig
 end

module type SAIL_INT =
 sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val abst : Z.t -> t

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

module Bits :
 sig
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

  val abst : Bits.t -> t

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

module type SAIL_BITS_INT =
 functor (Bits__3:SAIL_BITS) ->
 functor (Int:SAIL_INT) ->
 sig
  val unsigned : Bits__3.t -> Int.t

  val signed : Bits__3.t -> Int.t

  val zeros : Big_int_Z.big_int -> Int.t -> Bits__3.t

  val ones : Big_int_Z.big_int -> Int.t -> Bits__3.t

  val zero_extend : Big_int_Z.big_int -> Bits__3.t -> Int.t -> Bits__3.t

  val sign_extend : Big_int_Z.big_int -> Bits__3.t -> Int.t -> Bits__3.t

  val count_leading_zeros : Bits__3.t -> Int.t

  val count_trailing_zeros : Bits__3.t -> Int.t

  val bits_length : Bits__3.t -> Int.t
 end

module AstValue :
 sig
  type t = value
 end

module type SAIL_VALUE =
 sig
  type t

  val join : t -> t -> t

  val meet : t -> t -> t

  val top : t

  val bot : t

  val leb : t -> t -> bool

  val abst : AstValue.t -> t

  val is_unit : t -> bool

  val is_true : t -> bool

  val is_false : t -> bool

  val of_lit : lit -> t

  val mk_unit : unit -> t

  val mk_list : t list -> t

  val mk_tuple : t list -> t

  val mk_vector : t list -> t

  val mk_bitvector : t list -> t

  val mk_ref : id_aux -> t

  val mk_member : id_aux -> t

  val mk_ctor : id_aux -> t list -> t

  val cons : t -> t -> t

  val mk_record : (id_aux * t) list -> t

  val update_record : t -> (id_aux * t) list -> t option

  val lookup_field : t -> id_aux -> t

  module Matching :
   functor (Tannot:S) ->
   sig
    val pattern_match : Tannot.t pat -> t -> t match_result
   end

  val destructure_assignment : t destructure -> t -> (t place * t) list

  val update_place : t place -> t -> t -> t

  val place_root : t place -> id option

  val complete : t binding -> t
 end
