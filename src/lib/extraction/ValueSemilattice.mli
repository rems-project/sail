open Ast
open IdUtil
open PatternMatch
open TypeAnnot
open ValueType

module Value :
 functor (Tannot:S) ->
 sig
  type t = value

  val join : t -> t -> t

  val v_unit : value

  val v_list : value list -> value

  val v_tuple : value list -> value

  val v_vector : value list -> value

  val v_ref : id -> value

  val of_lit : lit -> value

  val is_unit : t -> bool

  val is_true : t -> bool

  val is_false : t -> bool

  val lookup_field' : (id * t) list -> id -> t

  val lookup_field : t -> id -> t

  module PM :
   sig
    val fold_match :
      (Tannot.t pat -> value -> value match_result) -> Tannot.t pat list ->
      (value match_result * value list) -> value match_result * value list

    val pattern_match : Tannot.t pat -> value -> value match_result
   end

  val pattern_match : Tannot.t pat -> t -> t match_result

  val complete : t binding -> t
 end
