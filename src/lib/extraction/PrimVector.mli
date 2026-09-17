open BinInt
open Datatypes
open List0
open ListDef

val take : Big_int_Z.big_int -> 'a1 list -> 'a1 list

val drop : Big_int_Z.big_int -> 'a1 list -> 'a1 list

val append : 'a1 list -> 'a1 list -> 'a1 list

val length : 'a1 list -> Big_int_Z.big_int

val vector_init : Big_int_Z.big_int -> 'a1 -> 'a1 list

val subrange : 'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list

val subrange_inc :
  'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list

val slice : 'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list

val slice_inc : 'a1 list -> Big_int_Z.big_int -> Big_int_Z.big_int -> 'a1 list

val vector_truncate : 'a1 list -> Big_int_Z.big_int -> 'a1 list

val vector_truncateLSB : 'a1 list -> Big_int_Z.big_int -> 'a1 list

val update_list : 'a1 list -> Big_int_Z.big_int -> 'a1 -> 'a1 list

val update_list_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 -> 'a1 list

val update : 'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list

val update_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list

val update_subrange : 'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list

val update_subrange_inc :
  'a1 list -> Big_int_Z.big_int -> 'a1 list -> 'a1 list

val replicate_bits : 'a1 list -> Big_int_Z.big_int -> 'a1 list

val reverse_endianness_fuel : Big_int_Z.big_int -> 'a1 list -> 'a1 list

val reverse_endianness : 'a1 list -> 'a1 list

val arith_shiftr : 'a1 list -> Big_int_Z.big_int -> 'a1 list

val access_inc : 'a1 list -> Big_int_Z.big_int -> 'a1 list

val access : 'a1 list -> Big_int_Z.big_int -> 'a1 list
