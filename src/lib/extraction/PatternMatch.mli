open Ast
open BinInt
open Bit
open Datatypes
open IdUtil
open List0
open ListDef
open ListUtil
open Nat0

type binding =
| Complete of value
| Partial of ((value * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty

val combine_binding : binding option -> binding option -> binding option

val merge_bindings : binding IdMap.t -> binding IdMap.t -> binding IdMap.t

val update_list : bit list -> Big_int_Z.big_int -> bit -> bit list

val update_subrange : bit list -> Big_int_Z.big_int -> bit list -> bit list

val complete_value :
  ((value * Big_int_Z.big_int) * Big_int_Z.big_int) non_empty -> value

val complete_bindings : binding IdMap.t -> value IdMap.t

type match_result =
| Matched of binding IdMap.t
| MaybeMatched of binding IdMap.t
| Unmatched

val merge_match_result : match_result -> match_result -> match_result

val empty_bindings : binding IdMap.t

val simple_match : match_result

val simple_match_when : bool -> match_result

val add_match : id -> binding -> match_result -> match_result

val neg_match : match_result -> match_result

val or_match : match_result -> match_result -> match_result

val binds_id : id -> 'a1 pat -> bool
