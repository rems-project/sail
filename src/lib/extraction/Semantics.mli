open Ast
open AstInduction
open Bit
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open PatternMatch
open PeanoNat
open Specif
open TypeAnnot
open ValueType
open Wf

val is_value : 'a1 exp -> bool

type return_value =
| Return_ok of value
| Return_exception of value

type var_type =
| Var_local
| Var_register

type place =
| PL_id of id * var_type
| PL_register of id
| PL_vector of place * Big_int_Z.big_int
| PL_vector_range of place * Big_int_Z.big_int * Big_int_Z.big_int
| PL_field of place * id

type destructure =
| DL_tuple of destructure list
| DL_vector_concat of (Types.vector_concat_split * destructure) list
| DL_place of place

module Monad :
 sig
  type 'a t =
  | Pure of 'a
  | Early_return of value
  | Exception of value
  | Runtime_type_error of Parse_ast.l
  | Match_failure of Parse_ast.l
  | Assertion_failed of string
  | Call of id * value list * (return_value -> 'a t)
  | Read_var of place * (value -> 'a t)
  | Write_var of place * value * (unit -> 'a t)
  | Get_undefined of typ * (value -> 'a t)

  val bind : 'a1 t -> ('a1 -> 'a2 t) -> 'a2 t

  val fmap : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val pure : 'a1 -> 'a1 t

  val lift_option : Parse_ast.l -> 'a1 option -> 'a1 t

  val sequence : 'a1 t list -> 'a1 list t

  val get_undefined : typ -> value t

  val throw : value -> 'a1 t

  type 'a caught =
  | Continue of 'a
  | Caught of value

  val catch : 'a1 t -> 'a1 caught t
 end

type 'a evaluated =
| Evaluated of 'a
| Unevaluated

val get_bool : 'a1 exp -> bool evaluated Monad.t

val get_string : 'a1 exp -> string evaluated Monad.t

val get_value : 'a1 exp -> value evaluated

val all_evaluated : 'a1 exp list -> value list

val coerce_place : Parse_ast.l -> destructure -> place Monad.t

val left_to_right : 'a1 exp list -> 'a1 exp list * 'a1 exp list

val all_evaluated_fields : 'a1 fexp list -> (id * value) list

val left_to_right_fields : 'a1 fexp list -> 'a1 fexp list * 'a1 fexp list

type 'a ltr2 =
| LTR2_0 of 'a exp * 'a exp
| LTR2_1 of value * 'a exp
| LTR2_2 of value * value

val left_to_right2 : 'a1 exp -> 'a1 exp -> 'a1 ltr2

type 'a ltr3 =
| LTR3_0 of 'a exp * 'a exp * 'a exp
| LTR3_1 of value * 'a exp * 'a exp
| LTR3_2 of value * value * 'a exp
| LTR3_3 of value * value * value

val left_to_right3 : 'a1 exp -> 'a1 exp -> 'a1 exp -> 'a1 ltr3

module Make :
 functor (Tannot:S) ->
 sig
  module PM :
   sig
    val fold_match :
      (Tannot.t pat -> value -> value match_result) -> Tannot.t pat list ->
      (value match_result * value list) -> value match_result * value list

    val pattern_match : Tannot.t pat -> value -> value match_result
   end

  val substitute : id -> value -> 'a1 exp -> 'a1 exp

  val substitute_arm : id -> value -> 'a1 pexp -> 'a1 pexp

  val substitute_lexp : id -> value -> 'a1 lexp -> 'a1 lexp

  val bv_concat : Parse_ast.l -> value list -> bit list Monad.t

  val lookup_field : Parse_ast.l -> id -> (id * value) list -> value Monad.t

  val destructuring_assignment :
    Tannot.t annot -> destructure -> value -> unit Monad.t

  val lexp_to_destructure : Tannot.t lexp -> destructure Monad.t

  val update_field : id -> value -> (id * value) list -> (id * value) list

  val step : Tannot.t exp -> Tannot.t exp Monad.t
 end
