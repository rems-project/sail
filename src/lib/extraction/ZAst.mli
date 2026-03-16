open Ast
open AstInduction
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open OptionUtil
open PatternMatch
open TypeAnnot

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

type match_case =
| Match
| Letbind
| Try
| Internal_plet

type ('v, 'r, 's, 'a) zexp_aux =
| Z_single of ('v, 'r, 's, 'a) zexp * single_case
| Z_return of ('v, 'r, 's, 'a) zexp
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

  val mk_single : Tannot.t annot -> single_case -> t -> Tannot.t exp

  val mk_var :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> Tannot.t exp

  val mk_assign :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> Tannot.t exp

  val mk_undef : Tannot.t annot -> Tannot.t exp
 end

module Residual :
 functor (Tannot:S) ->
 functor (L:sig
  type t

  val join : t -> t -> t

  val v_unit : t

  val v_list : t list -> t

  val v_tuple : t list -> t

  val v_vector : t list -> t

  val v_ref : id -> t

  val of_lit : lit -> t

  val is_unit : t -> bool

  val is_true : t -> bool

  val is_false : t -> bool

  val lookup_field : t -> id -> t

  val pattern_match : Tannot.t pat -> t -> t match_result

  val complete : t binding -> t
 end) ->
 functor (B:sig
  type t

  val mk_app : Tannot.t annot -> id -> t list -> t

  val mk_config : Tannot.t annot -> string list -> t

  val mk_id : Tannot.t annot -> id -> t

  val mk_block : Tannot.t annot -> t list -> t

  val mk_exit : Tannot.t annot -> t -> t

  val mk_ite : Tannot.t annot -> t -> t -> t -> t

  val mk_list : Tannot.t annot -> list_case -> t list -> t

  val mk_literal : Tannot.t annot -> lit -> t

  val mk_match :
    Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t) list
    -> t

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot.t annot -> id -> t

  val mk_return : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t
 end) ->
 sig
  type value = { this : L.t option; exn : L.t option; eff : bool }

  val this : value -> L.t option

  val exn : value -> L.t option

  val eff : value -> bool

  type state = { locals : L.t IdMap.t; registers : L.t IdMap.t }

  val locals : state -> L.t IdMap.t

  val registers : state -> L.t IdMap.t

  type t = value * B.t

  val is_unit : value -> bool

  val is_true : value -> bool

  val is_false : value -> bool

  val bounded_join : L.t option -> L.t option -> L.t option

  val mk_block : Tannot.t annot -> t list -> value * B.t

  val mk_exit : Tannot.t annot -> t -> value * B.t

  val mk_ite : Tannot.t annot -> t -> t -> t -> value * B.t

  val mk_list : Tannot.t annot -> list_case -> t list -> value * B.t

  val mk_literal : Tannot.t annot -> lit -> value * B.t

  val build_arm :
    (((state * Tannot.t pat) * t option) * t) -> (Tannot.t pat * B.t
    option) * B.t

  val exn_arm : (((state * Tannot.t pat) * t option) * t) -> L.t option

  val this_arm : (((state * Tannot.t pat) * t option) * t) -> L.t option

  val eff_arm : (((state * Tannot.t pat) * t option) * t) -> bool

  val mk_match :
    Tannot.t annot -> match_case -> bool -> t -> (((state * Tannot.t pat) * t
    option) * t) list -> t

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> value * B.t

  val mk_ref : Tannot.t annot -> id -> value * B.t

  val mk_return : Tannot.t annot -> t -> value * B.t

  val mk_single : Tannot.t annot -> single_case -> t -> value * B.t

  val mk_var :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> value * B.t

  val mk_assign :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> value * B.t

  val empty : state

  val join : state -> state -> state

  val from_semilattice : L.t -> value

  val pattern_match :
    l -> match_case -> Tannot.t pat -> t -> (Parse_ast.l, L.t match_result)
    sum

  val end_match : match_case -> state option -> state list -> state

  val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

  val assign : Tannot.t zlexp -> t list -> t -> state -> state
 end

module Make :
 functor (Tannot:S) ->
 functor (L:sig
  type t

  val join : t -> t -> t

  val v_unit : t

  val v_list : t list -> t

  val v_tuple : t list -> t

  val v_vector : t list -> t

  val v_ref : id -> t

  val of_lit : lit -> t

  val is_unit : t -> bool

  val is_true : t -> bool

  val is_false : t -> bool

  val lookup_field : t -> id -> t

  val pattern_match : Tannot.t pat -> t -> t match_result

  val complete : t binding -> t
 end) ->
 functor (B:sig
  type t

  val mk_app : Tannot.t annot -> id -> t list -> t

  val mk_config : Tannot.t annot -> string list -> t

  val mk_id : Tannot.t annot -> id -> t

  val mk_block : Tannot.t annot -> t list -> t

  val mk_exit : Tannot.t annot -> t -> t

  val mk_ite : Tannot.t annot -> t -> t -> t -> t

  val mk_list : Tannot.t annot -> list_case -> t list -> t

  val mk_literal : Tannot.t annot -> lit -> t

  val mk_match :
    Tannot.t annot -> match_case -> t -> ((Tannot.t pat * t option) * t) list
    -> t

  val mk_pair : Tannot.t annot -> pair_case -> t -> t -> t

  val mk_ref : Tannot.t annot -> id -> t

  val mk_return : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t
 end) ->
 sig
  module R :
   sig
    type value = { this : L.t option; exn : L.t option; eff : bool }

    val this : value -> L.t option

    val exn : value -> L.t option

    val eff : value -> bool

    type state = { locals : L.t IdMap.t; registers : L.t IdMap.t }

    val locals : state -> L.t IdMap.t

    val registers : state -> L.t IdMap.t

    type t = value * B.t

    val is_unit : value -> bool

    val is_true : value -> bool

    val is_false : value -> bool

    val bounded_join : L.t option -> L.t option -> L.t option

    val mk_block : Tannot.t annot -> t list -> value * B.t

    val mk_exit : Tannot.t annot -> t -> value * B.t

    val mk_ite : Tannot.t annot -> t -> t -> t -> value * B.t

    val mk_list : Tannot.t annot -> list_case -> t list -> value * B.t

    val mk_literal : Tannot.t annot -> lit -> value * B.t

    val build_arm :
      (((state * Tannot.t pat) * t option) * t) -> (Tannot.t pat * B.t
      option) * B.t

    val exn_arm : (((state * Tannot.t pat) * t option) * t) -> L.t option

    val this_arm : (((state * Tannot.t pat) * t option) * t) -> L.t option

    val eff_arm : (((state * Tannot.t pat) * t option) * t) -> bool

    val mk_match :
      Tannot.t annot -> match_case -> bool -> t -> (((state * Tannot.t
      pat) * t option) * t) list -> t

    val mk_pair : Tannot.t annot -> pair_case -> t -> t -> value * B.t

    val mk_ref : Tannot.t annot -> id -> value * B.t

    val mk_return : Tannot.t annot -> t -> value * B.t

    val mk_single : Tannot.t annot -> single_case -> t -> value * B.t

    val mk_var :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> value * B.t

    val mk_assign :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> value * B.t

    val empty : state

    val join : state -> state -> state

    val from_semilattice : L.t -> value

    val pattern_match :
      l -> match_case -> Tannot.t pat -> t -> (Parse_ast.l, L.t match_result)
      sum

    val end_match : match_case -> state option -> state list -> state

    val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

    val assign : Tannot.t zlexp -> t list -> t -> state -> state
   end

  module Monad :
   sig
    type 'a t =
    | Pure of 'a
    | Early_return of R.value * (unit -> 'a t)
    | Exit of R.value * (unit -> 'a t)
    | Call of id * R.value list * (R.value -> 'a t)
    | Get_config of string list * (R.value -> 'a t)
    | Runtime_type_error of Parse_ast.l
    | Get_undefined of typ * (R.value -> 'a t)

    val t_rect :
      ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) ->
      (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id -> R.value
      list -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> (string list
      -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> (Parse_ast.l ->
      'a2) -> (typ -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> 'a1 t
      -> 'a2

    val t_rec :
      ('a1 -> 'a2) -> (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) ->
      (R.value -> (unit -> 'a1 t) -> (unit -> 'a2) -> 'a2) -> (id -> R.value
      list -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> (string list
      -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> (Parse_ast.l ->
      'a2) -> (typ -> (R.value -> 'a1 t) -> (R.value -> 'a2) -> 'a2) -> 'a1 t
      -> 'a2

    val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

    val lift_sum : (Parse_ast.l, 'a1) sum -> 'a1 t
   end

  val pure : 'a1 -> 'a1 Monad.t

  type t = (L.t IdMap.t, R.t, R.state, Tannot.t) zexp

  val lookup : t -> id -> L.t option

  val down :
    t -> R.state -> Tannot.t exp -> ((t * R.state) * (Tannot.t exp, R.t) sum)
    Monad.t

  val next :
    (L.t IdMap.t, R.t, R.state, Tannot.t) zexp_aux -> Tannot.t annot ->
    R.state -> R.t -> ((t * R.state) * (Tannot.t exp, R.t) sum) Monad.t

  val step :
    t -> R.state -> (Tannot.t exp, R.t) sum -> ((t * R.state) * (Tannot.t
    exp, R.t) sum) Monad.t
 end
