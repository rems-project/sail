open Assignment
open Ast
open Datatypes
open IdUtil
open Lattice
open List0
open ListDef
open OptionUtil
open PatternMatch
open TypeAnnot
open Base

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
 functor (Tannot:S) ->
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

  val mk_inline : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 functor (L:SAIL_VALUE) ->
 sig
  module Matching :
   sig
    val pattern_match : Tannot.t pat -> L.t -> L.t match_result
   end

  module Destructure :
   sig
    val zlexp_to_destructure :
      'a1 list -> Tannot.t zlexp -> 'a1 destructure option * 'a1 list
   end

  type value = { this : L.t option; exn : L.t option; eff : bool }

  val this : value -> L.t option

  val exn : value -> L.t option

  val eff : value -> bool

  type state = { local_lets : L.t IdMap.t list;
                 local_vars : L.t IdMap.t list; toplevel_lets : L.t IdMap.t;
                 registers : L.t IdMap.t }

  val local_lets : state -> L.t IdMap.t list

  val local_vars : state -> L.t IdMap.t list

  val toplevel_lets : state -> L.t IdMap.t

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

  val join_returns : t option -> t -> t

  val mk_inline : Tannot.t annot -> t option -> t -> value * B.t

  val mk_single : Tannot.t annot -> single_case -> t -> value * B.t

  val mk_var :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> value * B.t

  val mk_assign :
    Tannot.t annot -> Tannot.t zlexp -> t list -> t -> value * B.t

  val known_fields : (id * t) list -> (id_aux * L.t) list option

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t

  val empty : state

  val join : state -> state -> state

  val from_semilattice : L.t -> value

  val pattern_match :
    l -> match_case -> Tannot.t pat -> t -> (Parse_ast.l, L.t match_result)
    sum

  val end_match : match_case -> state option -> state list -> state

  val push_scope : state -> state

  val pop_scope : state -> state

  val lookup_local_let : state -> id -> L.t option

  val lookup_local_var : state -> id -> L.t option

  val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

  val bind_arm : L.t IdMap.t -> state -> L.t option IdMap.t * state

  val restore_arm : L.t option IdMap.t -> state -> state

  val state_lookup : state -> id -> L.t

  val assign_id : id -> L.t -> state -> state

  val subexp_values : t list -> L.t list

  val assign_place : state -> (L.t place * L.t) -> state

  val assign : Tannot.t zlexp -> t list -> t -> state -> state
 end

module Make :
 functor (Tannot:S) ->
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

  val mk_inline : Tannot.t annot -> t -> t

  val mk_single : Tannot.t annot -> single_case -> t -> t

  val mk_var : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> t

  val mk_assign : Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t

  val mk_undef : Tannot.t annot -> t

  val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

  val mk_struct_update :
    Tannot.t annot -> struct_name -> t -> (id * t) list -> t
 end) ->
 functor (L:SAIL_VALUE) ->
 sig
  module R :
   sig
    module Matching :
     sig
      val pattern_match : Tannot.t pat -> L.t -> L.t match_result
     end

    module Destructure :
     sig
      val zlexp_to_destructure :
        'a1 list -> Tannot.t zlexp -> 'a1 destructure option * 'a1 list
     end

    type value = { this : L.t option; exn : L.t option; eff : bool }

    val this : value -> L.t option

    val exn : value -> L.t option

    val eff : value -> bool

    type state = { local_lets : L.t IdMap.t list;
                   local_vars : L.t IdMap.t list;
                   toplevel_lets : L.t IdMap.t; registers : L.t IdMap.t }

    val local_lets : state -> L.t IdMap.t list

    val local_vars : state -> L.t IdMap.t list

    val toplevel_lets : state -> L.t IdMap.t

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

    val join_returns : t option -> t -> t

    val mk_inline : Tannot.t annot -> t option -> t -> value * B.t

    val mk_single : Tannot.t annot -> single_case -> t -> value * B.t

    val mk_var :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> t -> value * B.t

    val mk_assign :
      Tannot.t annot -> Tannot.t zlexp -> t list -> t -> value * B.t

    val known_fields : (id * t) list -> (id_aux * L.t) list option

    val mk_struct : Tannot.t annot -> struct_name -> (id * t) list -> t

    val mk_struct_update :
      Tannot.t annot -> struct_name -> t -> (id * t) list -> t

    val empty : state

    val join : state -> state -> state

    val from_semilattice : L.t -> value

    val pattern_match :
      l -> match_case -> Tannot.t pat -> t -> (Parse_ast.l, L.t match_result)
      sum

    val end_match : match_case -> state option -> state list -> state

    val push_scope : state -> state

    val pop_scope : state -> state

    val lookup_local_let : state -> id -> L.t option

    val lookup_local_var : state -> id -> L.t option

    val lookup : Parse_ast.l -> state -> id -> (Parse_ast.l, L.t) sum

    val bind_arm : L.t IdMap.t -> state -> L.t option IdMap.t * state

    val restore_arm : L.t option IdMap.t -> state -> state

    val state_lookup : state -> id -> L.t

    val assign_id : id -> L.t -> state -> state

    val subexp_values : t list -> L.t list

    val assign_place : state -> (L.t place * L.t) -> state

    val assign : Tannot.t zlexp -> t list -> t -> state -> state
   end

  module Monad :
   sig
    type function_return =
    | Return_inlined of ((Tannot.t pat * Tannot.t exp option) * Tannot.t exp)
                        list
    | Return_value of R.value

    val function_return_rect :
      (((Tannot.t pat * Tannot.t exp option) * Tannot.t exp) list -> 'a1) ->
      (R.value -> 'a1) -> function_return -> 'a1

    val function_return_rec :
      (((Tannot.t pat * Tannot.t exp option) * Tannot.t exp) list -> 'a1) ->
      (R.value -> 'a1) -> function_return -> 'a1

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

  type t = (L.t option IdMap.t, R.t, R.state, Tannot.t) zexp

  val down :
    t -> R.state -> Tannot.t exp -> ((t * R.state) * (Tannot.t exp, R.t) sum)
    Monad.t

  val join_inline_return : R.t -> t -> t option

  val next :
    (L.t option IdMap.t, R.t, R.state, Tannot.t) zexp_aux -> Tannot.t annot
    -> R.state -> R.t -> ((t * R.state) * (Tannot.t exp, R.t) sum) Monad.t

  val step :
    t -> R.state -> (Tannot.t exp, R.t) sum -> ((t * R.state) * (Tannot.t
    exp, R.t) sum) Monad.t
 end
