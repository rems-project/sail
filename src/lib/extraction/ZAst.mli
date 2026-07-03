open AbsBitvector
open AbsValue
open Ast
open AstInduction
open BinInt
open Bit
open Datatypes
open IdUtil
open Interval
open List0
open ListDef
open ListUtil
open OptionUtil
open PatternMatch
open Qcanon
open SailBase
open TransferBitvectorInterval
open TypeAnnot
open Base
open Fin_maps
open Gmap

type 'a zlexp_aux =
| LZ_id of id
| LZ_deref
| LZ_app of id * Big_int_Z.big_int
| LZ_typ of typ * id
| LZ_tuple of 'a zlexp list
| LZ_vector_concat of 'a zlexp list
| LZ_vector of 'a zlexp
| LZ_vector_range of 'a zlexp
| LZ_field of 'a zlexp * id
and 'a zlexp =
| LZ_aux of 'a zlexp_aux * 'a annot

val lexp_to_z : 'a1 lexp -> 'a1 zlexp

val update_zlexp_subexps :
  'a1 exp list -> 'a1 zlexp -> 'a1 lexp option * 'a1 exp list

type single_case =
| Field of id
| Internal_assume of n_constraint
| Internal_return
| Throw
| Typ of typ

type pair_case =
| Assert
| Vector_append
| Cons

type list_case =
| List
| Tuple
| Vector
| Bitvector

type match_case =
| Match
| Letbind
| Try
| Internal_plet

type ('v, 'r, 's, 'a) zexp_aux =
| Z_single of ('v, 'r, 's, 'a) zexp * single_case
| Z_return of ('v, 'r, 's, 'a) zexp
| Z_inline of ('v, 'r, 's, 'a) zexp * 'r option
| Z_exit of ('v, 'r, 's, 'a) zexp
| Z_pair_1 of ('v, 'r, 's, 'a) zexp * pair_case * 'a exp
| Z_pair_2 of ('v, 'r, 's, 'a) zexp * pair_case * 'r
| Z_list of ('v, 'r, 's, 'a) zexp * list_case * 'r list * 'a exp list
| Z_app of ('v, 'r, 's, 'a) zexp * id * 'r list * 'a exp list
| Z_block of ('v, 'r, 's, 'a) zexp * 'r list * 'a exp list
| Z_if_cond of ('v, 'r, 's, 'a) zexp * 'a exp * 'a exp
| Z_if_then of ('v, 'r, 's, 'a) zexp * ('s * 'r) * 'a exp
| Z_if_else of ('v, 'r, 's, 'a) zexp * 'r * ('s * 'r)
| Z_match_head of ('v, 'r, 's, 'a) zexp * match_case
   * ((('s * 'a pat) * 'r option) * 'r) list
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_match_arms_guard of ('v, 'r, 's, 'a) zexp * match_case * 'v * ('s * 'r)
   * ((('s * 'a pat) * 'r option) * 'r) list * 'a pat * bool * 'a exp
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_match_arms_body of ('v, 'r, 's, 'a) zexp * match_case * 'v * ('s * 'r)
   * ((('s * 'a pat) * 'r option) * 'r) list * 'a pat * 'r option
   * (('a pat * 'a exp option) * 'a exp) list option
| Z_assign_left of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp list
   * 'a exp
| Z_assign_right of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list
| Z_var_left of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp list
   * 'a exp * 'a exp
| Z_var_right of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'a exp
| Z_var_body of ('v, 'r, 's, 'a) zexp * 'a zlexp * 'r list * 'r
| Z_struct of ('v, 'r, 's, 'a) zexp * struct_name * (id * 'r) list * 
   id * 'a fexp list
| Z_struct_update_base of ('v, 'r, 's, 'a) zexp * struct_name * 'a fexp list
| Z_struct_update of ('v, 'r, 's, 'a) zexp * struct_name * 'r
   * (id * 'r) list * id * 'a fexp list
and ('v, 'r, 's, 'a) zexp =
| Z_aux of ('v, 'r, 's, 'a) zexp_aux * 'a annot
| Z_top

val unwrap_arm : 'a1 pexp -> ('a1 pat * 'a1 exp option) * 'a1 exp

module ExpBuilder :
 functor (Tannot:S) ->
 sig
  type t = Tannot.t exp

  val mk_app : Tannot.t annot -> id -> t list -> Tannot.t exp

  val mk_config : Tannot.t annot -> string list -> Tannot.t exp

  val mk_id : Tannot.t annot -> id -> Tannot.t exp

  val mk_block : Tannot.t annot -> t list -> Tannot.t exp

  val mk_exit : Tannot.t annot -> t -> Tannot.t exp

  val mk_ite : Tannot.t annot -> t -> t -> t -> Tannot.t exp

  val mk_list : Tannot.t annot -> list_case -> t list -> Tannot.t exp

  val mk_literal : Tannot.t annot -> lit -> Tannot.t exp

  val mk_pexp :
    Tannot.t annot -> ((Tannot.t pat * t option) * t) -> Tannot.t pexp

  val mk_match :
    Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t) list
    -> Tannot.t exp

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> Tannot.t exp

  val mk_ref : Tannot.t annot -> id -> Tannot.t exp

  val mk_return : Tannot.t annot -> t -> Tannot.t exp

  val mk_inline : Tannot.t annot -> t -> Tannot.t exp

  val mk_single : Tannot.t annot -> single_case -> t -> Tannot.t exp

  val mk_var :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> Tannot.t exp

  val mk_assign :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> Tannot.t exp

  val mk_undef : Tannot.t annot -> Tannot.t exp

  val mk_fexp : Tannot.t annot -> (id * t) -> Tannot.t fexp

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t
 end

module Residual :
 functor (Tannot__3:S) ->
 functor (B:sig
  type t

  val mk_app : Tannot__3.t annot -> id -> t list -> t

  val mk_config : Tannot__3.t annot -> string list -> t

  val mk_id : Tannot__3.t annot -> id -> t

  val mk_block : Tannot__3.t annot -> t list -> t

  val mk_exit : Tannot__3.t annot -> t -> t

  val mk_ite : Tannot__3.t annot -> t -> t -> t -> t

  val mk_list : Tannot__3.t annot -> list_case -> t list -> t

  val mk_literal : Tannot__3.t annot -> lit -> t

  val mk_match :
    Tannot__3.t annot -> match_case -> t -> ((Tannot__3.t pat * t
    option) * t) list -> t

  val mk_pair : Tannot__3.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot__3.t annot -> id -> t

  val mk_return : Tannot__3.t annot -> t -> t

  val mk_inline : Tannot__3.t annot -> t -> t

  val mk_single : Tannot__3.t annot -> single_case -> t -> t

  val mk_var : Tannot__3.t annot -> Tannot__3.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot__3.t annot -> Tannot__3.t zlexp -> t list -> t -> t

  val mk_undef : Tannot__3.t annot -> t

  val mk_struct : Tannot__3.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot__3.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 sig
  module L :
   sig
    module DZP :
     sig
     end

    module DbvP :
     sig
     end

    type value =
    | V_bitvector of AbsBitvector.Dom.t
    | V_vector of value list
    | V_list of value list
    | V_int of Dom.t
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
      (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
      'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
      list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
      gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value)
      gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

    val value_rec :
      (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
      'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
      list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
      gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value)
      gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

    val mk_ctor : id_aux -> value list -> value

    val mk_member : id_aux -> value

    val is_unit : value -> bool

    val is_true : value -> bool

    val is_false : value -> bool

    type t = value

    val top : value

    val bot : t

    val value_length : value -> value

    val mk_bitvector' : value list -> AbsBitvector.Dom.t option

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

    val int_concrete : Dom.t -> Big_int_Z.big_int option

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
      val match_bitvector_lit :
        bit list -> AbsBitvector.Dom.t -> value match_result

      val pattern_match_literal : lit -> value -> value match_result

      val pattern_match : Tannot.t pat -> value -> value match_result
     end

    val complete_partial :
      ((t * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> t

    val complete : t binding -> t
   end

  module Matching :
   sig
    val match_bitvector_lit :
      bit list -> AbsBitvector.Dom.t -> L.value match_result

    val pattern_match_literal : lit -> L.value -> L.value match_result

    val pattern_match : Tannot__3.t pat -> L.value -> L.value match_result
   end

  type value = { this : L.t option; exn : L.t option; eff : bool }

  val this : value -> L.t option

  val exn : value -> L.t option

  val eff : value -> bool

  type state = { locals : L.t IdMap.t list; registers : L.t IdMap.t }

  val locals : state -> L.t IdMap.t list

  val registers : state -> L.t IdMap.t

  type t = value * B.t

  val is_unit : value -> bool

  val is_true : value -> bool

  val is_false : value -> bool

  val bounded_join : L.t option -> L.t option -> L.t option

  val mk_block : Tannot__3.t annot -> t list -> value * B.t

  val mk_exit : Tannot__3.t annot -> t -> value * B.t

  val mk_ite : Tannot__3.t annot -> t -> t -> t -> value * B.t

  val mk_list : Tannot__3.t annot -> list_case -> t list -> value * B.t

  val mk_literal : Tannot__3.t annot -> lit -> value * B.t

  val build_arm :
    (((state * Tannot__3.t pat) * t option) * t) -> (Tannot__3.t pat * B.t
    option) * B.t

  val exn_arm : (((state * Tannot__3.t pat) * t option) * t) -> L.t option

  val this_arm : (((state * Tannot__3.t pat) * t option) * t) -> L.t option

  val eff_arm : (((state * Tannot__3.t pat) * t option) * t) -> bool

  val mk_match :
    Tannot__3.t annot -> match_case -> bool -> t -> (((state * Tannot__3.t
    pat) * t option) * t) list -> t

  val mk_pair : Tannot__3.t annot -> pair_case -> t -> t -> value * B.t

  val mk_ref : Tannot__3.t annot -> id -> value * B.t

  val mk_return : Tannot__3.t annot -> t -> value * B.t

  val join_returns : t option -> t -> t

  val mk_inline : Tannot__3.t annot -> t option -> t -> value * B.t

  val mk_single : Tannot__3.t annot -> single_case -> t -> value * B.t

  val mk_var :
    Tannot__3.t annot -> Tannot__3.t zlexp -> t list -> t -> t -> value * B.t

  val mk_assign :
    Tannot__3.t annot -> Tannot__3.t zlexp -> t list -> t -> value * B.t

  val mk_struct : Tannot__3.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot__3.t annot -> struct_name -> t -> (id * t) list -> t

  val empty : state

  val join : state -> state -> state

  val from_semilattice : L.t -> value

  val pattern_match :
    l -> match_case -> Tannot__3.t pat -> t -> (Parse_ast.l, L.t
    match_result) sum

  val end_match : match_case -> state option -> state list -> state

  val push_scope : state -> state

  val pop_scope : state -> state

  val lookup_local : Parse_ast.l -> L.t IdMap.t list -> id -> L.t option

  val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

  type update_step =
  | US_field of id_aux
  | US_index of Big_int_Z.big_int
  | US_range of Big_int_Z.big_int * Big_int_Z.big_int

  val update_step_rect :
    (id_aux -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> (Big_int_Z.big_int ->
    Big_int_Z.big_int -> 'a1) -> update_step -> 'a1

  val update_step_rec :
    (id_aux -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> (Big_int_Z.big_int ->
    Big_int_Z.big_int -> 'a1) -> update_step -> 'a1

  val apply_path : L.t -> update_step list -> L.t -> L.t

  val subexp_concrete_z : t -> Big_int_Z.big_int option

  val zlexp_path :
    Tannot__3.t zlexp -> t list -> ((id * update_step list) * t list) option

  val state_lookup : state -> id -> L.t

  val assign_id : id -> L.t -> state -> state

  val assign_via_path : Tannot__3.t zlexp -> t list -> L.t -> state -> state

  val last_update_step : update_step list -> update_step option

  val zlexp_subwidth : Tannot__3.t zlexp -> t list -> Big_int_Z.big_int option

  val assign_value :
    Tannot__3.t zlexp -> t list -> L.t -> state -> state * t list

  val assign : Tannot__3.t zlexp -> t list -> t -> state -> state
 end

module Make :
 functor (Tannot__5:S) ->
 functor (B:sig
  type t

  val mk_app : Tannot__5.t annot -> id -> t list -> t

  val mk_config : Tannot__5.t annot -> string list -> t

  val mk_id : Tannot__5.t annot -> id -> t

  val mk_block : Tannot__5.t annot -> t list -> t

  val mk_exit : Tannot__5.t annot -> t -> t

  val mk_ite : Tannot__5.t annot -> t -> t -> t -> t

  val mk_list : Tannot__5.t annot -> list_case -> t list -> t

  val mk_literal : Tannot__5.t annot -> lit -> t

  val mk_match :
    Tannot__5.t annot -> match_case -> t -> ((Tannot__5.t pat * t
    option) * t) list -> t

  val mk_pair : Tannot__5.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot__5.t annot -> id -> t

  val mk_return : Tannot__5.t annot -> t -> t

  val mk_inline : Tannot__5.t annot -> t -> t

  val mk_single : Tannot__5.t annot -> single_case -> t -> t

  val mk_var : Tannot__5.t annot -> Tannot__5.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot__5.t annot -> Tannot__5.t zlexp -> t list -> t -> t

  val mk_undef : Tannot__5.t annot -> t

  val mk_struct : Tannot__5.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot__5.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 sig
  module R :
   sig
    module L :
     sig
      module DZP :
       sig
       end

      module DbvP :
       sig
       end

      type value =
      | V_bitvector of AbsBitvector.Dom.t
      | V_vector of value list
      | V_list of value list
      | V_int of Dom.t
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
        (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
        'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
        list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
        gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux,
        value) gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

      val value_rec :
        (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
        'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
        list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
        gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux,
        value) gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

      val mk_ctor : id_aux -> value list -> value

      val mk_member : id_aux -> value

      val is_unit : value -> bool

      val is_true : value -> bool

      val is_false : value -> bool

      type t = value

      val top : value

      val bot : t

      val value_length : value -> value

      val mk_bitvector' : value list -> AbsBitvector.Dom.t option

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

      val int_concrete : Dom.t -> Big_int_Z.big_int option

      val bv_slice : value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value

      val set_field : value -> id_aux -> value -> value

      val vector_update :
        value list -> Big_int_Z.big_int -> value -> value list

      val set_bv_range :
        value -> Big_int_Z.big_int -> Big_int_Z.big_int -> value -> value

      val get_vector_elem : value -> Big_int_Z.big_int -> value

      val set_vector_elem : value -> Big_int_Z.big_int -> value -> value

      module Matching :
       functor (Tannot:S) ->
       sig
        val match_bitvector_lit :
          bit list -> AbsBitvector.Dom.t -> value match_result

        val pattern_match_literal : lit -> value -> value match_result

        val pattern_match : Tannot.t pat -> value -> value match_result
       end

      val complete_partial :
        ((t * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> t

      val complete : t binding -> t
     end

    module Matching :
     sig
      val match_bitvector_lit :
        bit list -> AbsBitvector.Dom.t -> L.value match_result

      val pattern_match_literal : lit -> L.value -> L.value match_result

      val pattern_match : Tannot__5.t pat -> L.value -> L.value match_result
     end

    type value = { this : L.t option; exn : L.t option; eff : bool }

    val this : value -> L.t option

    val exn : value -> L.t option

    val eff : value -> bool

    type state = { locals : L.t IdMap.t list; registers : L.t IdMap.t }

    val locals : state -> L.t IdMap.t list

    val registers : state -> L.t IdMap.t

    type t = value * B.t

    val is_unit : value -> bool

    val is_true : value -> bool

    val is_false : value -> bool

    val bounded_join : L.t option -> L.t option -> L.t option

    val mk_block : Tannot__5.t annot -> t list -> value * B.t

    val mk_exit : Tannot__5.t annot -> t -> value * B.t

    val mk_ite : Tannot__5.t annot -> t -> t -> t -> value * B.t

    val mk_list : Tannot__5.t annot -> list_case -> t list -> value * B.t

    val mk_literal : Tannot__5.t annot -> lit -> value * B.t

    val build_arm :
      (((state * Tannot__5.t pat) * t option) * t) -> (Tannot__5.t pat * B.t
      option) * B.t

    val exn_arm : (((state * Tannot__5.t pat) * t option) * t) -> L.t option

    val this_arm : (((state * Tannot__5.t pat) * t option) * t) -> L.t option

    val eff_arm : (((state * Tannot__5.t pat) * t option) * t) -> bool

    val mk_match :
      Tannot__5.t annot -> match_case -> bool -> t -> (((state * Tannot__5.t
      pat) * t option) * t) list -> t

    val mk_pair : Tannot__5.t annot -> pair_case -> t -> t -> value * B.t

    val mk_ref : Tannot__5.t annot -> id -> value * B.t

    val mk_return : Tannot__5.t annot -> t -> value * B.t

    val join_returns : t option -> t -> t

    val mk_inline : Tannot__5.t annot -> t option -> t -> value * B.t

    val mk_single : Tannot__5.t annot -> single_case -> t -> value * B.t

    val mk_var :
      Tannot__5.t annot -> Tannot__5.t zlexp -> t list -> t -> t ->
      value * B.t

    val mk_assign :
      Tannot__5.t annot -> Tannot__5.t zlexp -> t list -> t -> value * B.t

    val mk_struct : Tannot__5.t annot -> struct_name -> (id * t) list -> t

    val mk_struct_update :
      Tannot__5.t annot -> struct_name -> t -> (id * t) list -> t

    val empty : state

    val join : state -> state -> state

    val from_semilattice : L.t -> value

    val pattern_match :
      l -> match_case -> Tannot__5.t pat -> t -> (Parse_ast.l, L.t
      match_result) sum

    val end_match : match_case -> state option -> state list -> state

    val push_scope : state -> state

    val pop_scope : state -> state

    val lookup_local : Parse_ast.l -> L.t IdMap.t list -> id -> L.t option

    val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

    type update_step =
    | US_field of id_aux
    | US_index of Big_int_Z.big_int
    | US_range of Big_int_Z.big_int * Big_int_Z.big_int

    val update_step_rect :
      (id_aux -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> 'a1) -> update_step -> 'a1

    val update_step_rec :
      (id_aux -> 'a1) -> (Big_int_Z.big_int -> 'a1) -> (Big_int_Z.big_int ->
      Big_int_Z.big_int -> 'a1) -> update_step -> 'a1

    val apply_path : L.t -> update_step list -> L.t -> L.t

    val subexp_concrete_z : t -> Big_int_Z.big_int option

    val zlexp_path :
      Tannot__5.t zlexp -> t list -> ((id * update_step list) * t list) option

    val state_lookup : state -> id -> L.t

    val assign_id : id -> L.t -> state -> state

    val assign_via_path : Tannot__5.t zlexp -> t list -> L.t -> state -> state

    val last_update_step : update_step list -> update_step option

    val zlexp_subwidth :
      Tannot__5.t zlexp -> t list -> Big_int_Z.big_int option

    val assign_value :
      Tannot__5.t zlexp -> t list -> L.t -> state -> state * t list

    val assign : Tannot__5.t zlexp -> t list -> t -> state -> state
   end

  module L :
   sig
    module DZP :
     sig
     end

    module DbvP :
     sig
     end

    type value = R.L.value =
    | V_bitvector of AbsBitvector.Dom.t
    | V_vector of value list
    | V_list of value list
    | V_int of Dom.t
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
      (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
      'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
      list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
      gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value)
      gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

    val value_rec :
      (AbsBitvector.Dom.t -> 'a1) -> (value list -> 'a1) -> (value list ->
      'a1) -> (Dom.t -> 'a1) -> (coq_Qc -> 'a1) -> (bool -> 'a1) -> (value
      list -> 'a1) -> 'a1 -> (string -> 'a1) -> (id_aux -> 'a1) -> (id_aux
      gset -> 'a1) -> ((id_aux, value list) gmap -> 'a1) -> ((id_aux, value)
      gmap -> 'a1) -> 'a1 -> 'a1 -> value -> 'a1

    val mk_ctor : id_aux -> value list -> value

    val mk_member : id_aux -> value

    val is_unit : value -> bool

    val is_true : value -> bool

    val is_false : value -> bool

    type t = value

    val top : value

    val bot : t

    val value_length : value -> value

    val mk_bitvector' : value list -> AbsBitvector.Dom.t option

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

    val int_concrete : Dom.t -> Big_int_Z.big_int option

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
      val match_bitvector_lit :
        bit list -> AbsBitvector.Dom.t -> value match_result

      val pattern_match_literal : lit -> value -> value match_result

      val pattern_match : Tannot.t pat -> value -> value match_result
     end

    val complete_partial :
      ((t * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> t

    val complete : t binding -> t
   end

  module Monad :
   sig
    type function_return =
    | Return_inlined of ((Tannot__5.t pat * Tannot__5.t exp
                        option) * Tannot__5.t exp) list
    | Return_value of R.value

    val function_return_rect :
      (((Tannot__5.t pat * Tannot__5.t exp option) * Tannot__5.t exp) list ->
      'a1) -> (R.value -> 'a1) -> function_return -> 'a1

    val function_return_rec :
      (((Tannot__5.t pat * Tannot__5.t exp option) * Tannot__5.t exp) list ->
      'a1) -> (R.value -> 'a1) -> function_return -> 'a1

    type 'a t =
    | Pure of 'a
    | Early_return of R.value * (unit -> 'a t)
    | Exit of R.value * (unit -> 'a t)
    | Call of id * R.value list * (function_return -> 'a t)
    | Get_config of string list * (R.value -> 'a t)
    | Runtime_type_error of Parse_ast.l
    | Get_undefined of typ * (R.value -> 'a t)

    val t_rect :
      ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) ->
      (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id -> R.value
      list -> (function_return -> 'a1 t) -> (function_return -> 'a2) -> 'a2)
      -> (string list -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) ->
      (Parse_ast.l -> 'a2) -> (typ -> (R.value -> 'a1 t) -> (R.value -> 'a2)
      -> 'a2) -> 'a1 t -> 'a2

    val t_rec :
      ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) ->
      (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id -> R.value
      list -> (function_return -> 'a1 t) -> (function_return -> 'a2) -> 'a2)
      -> (string list -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) ->
      (Parse_ast.l -> 'a2) -> (typ -> (R.value -> 'a1 t) -> (R.value -> 'a2)
      -> 'a2) -> 'a1 t -> 'a2

    val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

    val lift_sum : (Parse_ast.l, 'a1) sum -> 'a1 t
   end

  val pure : 'a1 -> 'a1 Monad.t

  type t = (L.t IdMap.t, R.t, R.state, Tannot__5.t) zexp

  val lookup : t -> id -> L.t option

  val down :
    t -> R.state -> Tannot__5.t exp -> ((t * R.state) * (Tannot__5.t exp,
    R.t) sum) Monad.t

  val join_inline_return : R.t -> t -> t option

  val next :
    (L.t IdMap.t, R.t, R.state, Tannot__5.t) zexp_aux -> Tannot__5.t annot ->
    R.state -> R.t -> ((t * R.state) * (Tannot__5.t exp, R.t) sum) Monad.t

  val step :
    t -> R.state -> (Tannot__5.t exp, R.t) sum ->
    ((t * R.state) * (Tannot__5.t exp, R.t) sum) Monad.t
 end
