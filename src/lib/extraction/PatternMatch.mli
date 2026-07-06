open Ast
open BinInt
open Bit
open BitList
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open Nat0
open PeanoNat
open QArith_base
open TypeAnnot

type 'v binding =
| Complete of 'v
| Partial of (('v * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty

val combine_binding :
  'a1 binding option -> 'a1 binding option -> 'a1 binding option

val merge_bindings :
  'a1 binding IdMap.t -> 'a1 binding IdMap.t -> 'a1 binding IdMap.t

val update_list : bit list -> Big_int_Z.big_int -> bit -> bit list

val update_subrange : bit list -> Big_int_Z.big_int -> bit list -> bit list

val complete_value :
  ((value * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> value

val complete_bindings : value binding IdMap.t -> value IdMap.t

type 'v match_result =
| Matched of 'v binding IdMap.t
| MaybeMatched of 'v binding IdMap.t
| Unmatched

val merge_match_result :
  'a1 match_result -> 'a1 match_result -> 'a1 match_result

val empty_bindings : 'a1 binding IdMap.t

val simple_match : 'a1 match_result

val simple_match_when : bool -> 'a1 match_result

val add_match : id -> 'a1 binding -> 'a1 match_result -> 'a1 match_result

val neg_match : 'a1 match_result -> 'a1 match_result

val or_match : value match_result -> value match_result -> value match_result

val binds_id : id -> 'a1 pat -> bool

val pattern_match_literal : lit -> value -> value match_result

val get_struct_field : id -> (id * value) list -> value

module Typed :
 functor (Tannot:S) ->
 sig
  val fold_match :
    (Tannot.t pat -> value -> value match_result) -> Tannot.t pat list ->
    (value match_result * value list) -> value match_result * value list

  val pattern_match : Tannot.t pat -> value -> value match_result
 end
