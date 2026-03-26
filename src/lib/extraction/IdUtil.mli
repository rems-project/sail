open Ast
open Datatypes
open FMapList
open OrdersAlt
open SailBase
open String0
open Base
open Countable

module Aux :
 sig
  type t = id_aux

  val unwrap : id -> t

  val eqb : t -> t -> bool

  val id_aux_eqdecb : t coq_EqDecb

  val encode_id_aux : t -> Big_int_Z.big_int

  val decode_id_aux : Big_int_Z.big_int -> t option

  val eq_dec : t -> t -> bool

  val eq_eqdec : (t, t) coq_RelDecision

  val id_aux_countable : t coq_Countable
 end

val id_eqb : id -> id -> bool

val id_ltb : id -> id -> bool

module IdOrdered :
 sig
  type t = id

  val compare : id -> id -> comparison

  val eq_dec : t -> t -> bool
 end

module IdOrderOrig :
 sig
  type t = id

  val eq_dec : id -> id -> bool

  val compare : id -> id -> id OrderedType.coq_Compare
 end

module IdMap :
 sig
  module Raw :
   sig
    module MX :
     sig
      module TO :
       sig
        type t = id
       end

      module IsTO :
       sig
       end

      module OrderTac :
       sig
       end

      val eq_dec : id -> id -> bool

      val lt_dec : id -> id -> bool

      val eqb : id -> id -> bool
     end

    module PX :
     sig
      module MO :
       sig
        module TO :
         sig
          type t = id
         end

        module IsTO :
         sig
         end

        module OrderTac :
         sig
         end

        val eq_dec : id -> id -> bool

        val lt_dec : id -> id -> bool

        val eqb : id -> id -> bool
       end
     end

    type key = id

    type 'elt t = (id * 'elt) list

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val mem : key -> 'a1 t -> bool

    val find : key -> 'a1 t -> 'a1 option

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    val remove : key -> 'a1 t -> 'a1 t

    val elements : 'a1 t -> 'a1 t

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

    val map2_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

    val map2_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

    val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1 * 'a2) list -> 'a3 -> 'a3

    val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
      (key * 'a3) list

    val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option
   end

  module E :
   sig
    type t = id

    val compare : id -> id -> id OrderedType.coq_Compare

    val eq_dec : id -> id -> bool
   end

  type key = id

  type 'elt slist = { this : 'elt Raw.t }

  val this : 'a1 slist -> 'a1 Raw.t

  type 'elt t = 'elt slist

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> Big_int_Z.big_int

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end
