open Ast
open AstInduction
open Datatypes
open IdUtil
open List0
open ListDef
open PeanoNat
open Specif
open Value_type
open Wf

type binding =
| Complete of value
| Partial of ((value * Big_int_Z.big_int) * Big_int_Z.big_int) list

val combine_binding : binding option -> binding option -> binding option

val merge_bindings : binding IdMap.t -> binding IdMap.t -> binding IdMap.t

val to_gvector : value -> value

val is_value : 'a1 exp -> bool

type return_value =
| Return_ok of value
| Return_exception of value

type var_type =
| Var_local
| Var_register

type id_type =
| Local_variable
| Global_register
| Enum_member

type place =
| PL_id of id * var_type
| PL_register of string
| PL_vector of place * Big_int_Z.big_int
| PL_vector_range of place * Big_int_Z.big_int * Big_int_Z.big_int
| PL_field of place * id

type vector_concat_split =
| No_split
| Split of Big_int_Z.big_int

type destructure =
| DL_app of id * value list
| DL_tuple of destructure list
| DL_vector_concat of (vector_concat_split * destructure) list
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

val all_evaluated_fields :
  (id -> string) -> 'a1 fexp list -> (string * value) list

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

val bitlist_of_hex_digit : hex_digit -> bit list

val hex_digit_of_nibble : bit -> bit -> bit -> bit -> hex_digit

val hex_digits_of_bitlist : bit list -> hex_digit list option

val non_empty_to_list : 'a1 non_empty -> 'a1 list

val bitlist_of_hex_lit : hex_digit non_empty list -> bit list

val bitlist_of_bin_lit : bin_digit non_empty list -> bit list

module type SemanticExt =
 sig
  type tannot

  val get_type : tannot -> typ

  val get_id_type : tannot -> id -> id_type

  val get_split : tannot -> vector_concat_split

  val is_bitvector : tannot -> bool

  val num_equal : Big_int_Z.big_int -> Big_int_Z.big_int -> bool

  val rational_equal : Rational.t -> Rational.t -> bool

  val id_equal_string : id -> string -> bool

  val string_of_id : id -> string

  val rational_of_string : string -> Rational.t

  val fallthrough : tannot pexp

  val complete_value :
    ((value * Big_int_Z.big_int) * Big_int_Z.big_int) list -> value
 end

module Make :
 functor (T:SemanticExt) ->
 sig
  val binds_id : id -> 'a1 pat -> bool

  val substitute : id -> value -> 'a1 exp -> 'a1 exp

  val substitute_arm : id -> value -> 'a1 pexp -> 'a1 pexp

  val substitute_lexp : id -> value -> 'a1 lexp -> 'a1 lexp

  val bv_concat : Parse_ast.l -> value list -> bit list Monad.t

  val value_of_lit : lit -> typ -> value Monad.t

  val same_bits : bit list -> bit list -> bool

  val pattern_match_literal : lit -> value -> bool

  val get_struct_field : string -> (string * value) list -> value

  val no_match : bool * binding IdMap.t

  val empty_bindings : binding IdMap.t

  val complete_bindings : binding IdMap.t -> value IdMap.t

  val pattern_match : T.tannot pat -> value -> bool * binding IdMap.t

  val lookup_field :
    Parse_ast.l -> string -> (string * value) list -> value Monad.t

  val destructuring_assignment :
    T.tannot annot -> destructure -> value -> unit Monad.t

  val lexp_to_destructure : T.tannot lexp -> destructure Monad.t

  val update_field :
    string -> value -> (string * value) list -> (string * value) list

  val step : T.tannot exp -> T.tannot exp Monad.t
 end
