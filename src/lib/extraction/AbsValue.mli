open Ast
open BinInt
open BinNat
open Bit
open BitList
open Datatypes
open IdUtil
open Lattice
open List0
open ListDef
open ListUtil
open Nat0
open OptionUtil
open PatternMatch
open PeanoNat
open QArith_base
open Qcanon
open SailBase
open TypeAnnot
open ValueType
open Base
open Decidable
open Fin_maps
open Fin_sets
open Gmap
open List_basics
open Option

module Dom :
 functor (DZ:SAIL_INT) ->
 functor (Dbv:SAIL_BITS) ->
 functor (T:sig
  val unsigned : Dbv.t -> DZ.t

  val signed : Dbv.t -> DZ.t

  val zeros : Big_int_Z.big_int -> DZ.t -> Dbv.t

  val ones : Big_int_Z.big_int -> DZ.t -> Dbv.t

  val zero_extend : Big_int_Z.big_int -> Dbv.t -> DZ.t -> Dbv.t

  val sign_extend : Big_int_Z.big_int -> Dbv.t -> DZ.t -> Dbv.t

  val count_leading_zeros : Dbv.t -> DZ.t

  val count_trailing_zeros : Dbv.t -> DZ.t

  val bits_length : Dbv.t -> DZ.t
 end) ->
 sig
  module DZP :
   sig
   end

  module DbvP :
   sig
   end

  type value =
  | V_bitvector of Dbv.t
  | V_vector of value list
  | V_list of value list
  | V_int of DZ.t
  | V_real of coq_Qc
  | V_bool of bool
  | V_tuple of value list
  | V_unit
  | V_string of string
  | V_ref of id_aux
  | V_member of id_aux gset
  | V_ctor of (id_aux, value list) gmap
  | V_record of (id_aux, value) gmap
  | V_top
  | V_bot

  val value_rect :
    (Dbv.t -> 'a1) -> (value list -> 'a1) -> (value list -> 'a1) -> (DZ.t ->
    'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value list -> 'a1) -> 'a1 ->
    (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux gset -> 'a1) -> ((id_aux,
    value list) gmap -> 'a1) -> ((id_aux, value) gmap -> 'a1) -> 'a1 -> 'a1
    -> value -> 'a1

  val value_rec :
    (Dbv.t -> 'a1) -> (value list -> 'a1) -> (value list -> 'a1) -> (DZ.t ->
    'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value list -> 'a1) -> 'a1 ->
    (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux gset -> 'a1) -> ((id_aux,
    value list) gmap -> 'a1) -> ((id_aux, value) gmap -> 'a1) -> 'a1 -> 'a1
    -> value -> 'a1

  val mk_ctor : id_aux -> value list -> value

  val mk_member : id_aux -> value

  val is_unit : value -> bool

  val is_true : value -> bool

  val is_false : value -> bool

  type t = value

  val top : value

  val bot : t

  val value_length : value -> value

  val mk_bitvector' : value list -> Dbv.t option

  val mk_bitvector : value list -> value

  val vdepth : value -> Big_int_Z.big_int

  val key_inter : (id_aux, 'a1) gmap -> (id_aux, 'a1) gmap -> id_aux list

  val ctor_compat :
    (id_aux, value list) gmap -> (id_aux, value list) gmap -> bool

  val same_or : 'a1 coq_EqDecb -> t -> ('a1 -> t) -> 'a1 -> 'a1 -> t

  val join : value -> value -> value

  val meet : value -> value -> value

  val leb : value -> value -> bool

  val abst : Ast.value -> value

  val of_lit : lit -> value

  val lookup_field : value -> id_aux -> value

  val int_concrete : DZ.t -> Big_int_Z.big_int option

  val bv_slice : value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value

  val set_field : value -> id_aux -> value -> value

  val vector_update : value list -> Big_int_Z.big_int -> value -> value list

  val set_bv_range :
    value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value -> value

  val get_vector_elem : value -> Big_int_Z.big_int -> value

  val set_vector_elem : value -> Big_int_Z.big_int -> value -> value

  module Matching :
   functor (Tannot:S) ->
   sig
    val match_bitvector_lit : bit list -> Dbv.t -> value match_result

    val pattern_match_literal : lit -> value -> value match_result

    val pattern_match : Tannot.t pat -> value -> value match_result
   end

  val complete_partial :
    ((t * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> t

  val complete : t binding -> t
 end
