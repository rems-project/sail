open BinInt
open BinNat
open Bit
open Bool
open Datatypes
open List0
open ListDef
open ListUtil
open PrimVector
open Definitions

val length : bvn -> Big_int_Z.big_int

val and_bit : bit -> bit -> bit

val or_bit : bit -> bit -> bit

val xor_bit : bit -> bit -> bit

val not_bit : bit -> bit

val add_bit_with_carry : bit -> bit -> bit -> bit * bit

val sub_bit_with_carry : bit -> bit -> bit -> bit * bit

val bool_of_bit : bit -> bool

val bit_of_bool : bool -> bit

val string_of_bit : bit -> string

val char_of_bit : bit -> char

val bigint_of_bit : bit -> Big_int_Z.big_int

val and_bool : bool -> bool -> bool

val or_bool : bool -> bool -> bool

val xor_bool : bool -> bool -> bool

val eq_bool : bool -> bool -> bool

val of_bit_list : bit list -> bvn

val to_bit_list : bvn -> bit list

val width : bvn -> Big_int_Z.big_int

val bits_eqb : bit list -> bit list -> bool

val lift1 : (Big_int_Z.big_int -> bv -> bv) -> bvn -> bvn

val lift2 : (Big_int_Z.big_int -> bv -> bv -> bv) -> bvn -> bvn -> bvn option

val not_vec : bvn -> bvn

val and_vec : bvn -> bvn -> bvn option

val or_vec : bvn -> bvn -> bvn option

val xor_vec : bvn -> bvn -> bvn option

val uint : bvn -> Big_int_Z.big_int

val sint : bvn -> Big_int_Z.big_int

val zeros : Big_int_Z.big_int -> bvn

val ones : Big_int_Z.big_int -> bvn

val zrange : Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int list

val zero_extend : bvn -> Big_int_Z.big_int -> bvn

val sign_extend : bvn -> Big_int_Z.big_int -> bvn

val shiftr : bvn -> Big_int_Z.big_int -> bvn

val shiftl : bvn -> Big_int_Z.big_int -> bvn

val arith_shiftr : bvn -> Big_int_Z.big_int -> bvn

val shiftr_ref : bit list -> Big_int_Z.big_int -> bit list

val shiftl_ref : bit list -> Big_int_Z.big_int -> bit list

val arith_shiftr_ref : bit list -> Big_int_Z.big_int -> bit list

val shift_bits_right : bvn -> bvn -> bvn

val shift_bits_left : bvn -> bvn -> bvn

val shift_bits_right_arith : bvn -> bvn -> bvn

val get_slice_int :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val to_bits : Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val get_slice_int_ref_aux :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bit list

val get_slice_int_ref :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bit list

val to_bits_ref : Big_int_Z.big_int -> Big_int_Z.big_int -> bit list

val add_vec : bvn -> bvn -> bvn option

val sub_vec : bvn -> bvn -> bvn option

val add_vec_int : bvn -> Big_int_Z.big_int -> bvn

val sub_vec_int : bvn -> Big_int_Z.big_int -> bvn

val count_leading_zeros : bvn -> Big_int_Z.big_int

val count_trailing_zeros : bvn -> Big_int_Z.big_int

val count_leading_zeros_ref : bit list -> Big_int_Z.big_int

val count_trailing_zeros_ref : bit list -> Big_int_Z.big_int

val append : bvn -> bvn -> bvn

val eq_bits : bvn -> bvn -> bool

val mult_vec : bvn -> bvn -> bvn

val mults_vec : bvn -> bvn -> bvn

val subrange : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val slice : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val access : bvn -> Big_int_Z.big_int -> bvn

val update_bit : bvn -> Big_int_Z.big_int -> bit -> bvn

val update_subrange :
  bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn -> bvn

val set_slice : bvn -> Big_int_Z.big_int -> bvn -> bvn

val set_slice_int :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn ->
  Big_int_Z.big_int

val set_slice_int_ref :
  Big_int_Z.big_int -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn ->
  Big_int_Z.big_int

val subrange_inc : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val slice_inc : bvn -> Big_int_Z.big_int -> Big_int_Z.big_int -> bvn

val access_inc : bvn -> Big_int_Z.big_int -> bvn

val update_bit_inc : bvn -> Big_int_Z.big_int -> bit -> bvn

val add_vec_carry : bvn -> bvn -> (bit * bvn) option

val replicate_bits_aux : Big_int_Z.big_int -> bvn -> bvn -> bvn

val replicate_bits : bvn -> Big_int_Z.big_int -> bvn

val vector_truncate : bvn -> Big_int_Z.big_int -> bvn

val vector_truncateLSB : bvn -> Big_int_Z.big_int -> bvn

val reverse_endianness_fuel : Big_int_Z.big_int -> bvn -> bvn

val reverse_endianness : bvn -> bvn

val split_at : Big_int_Z.big_int -> bvn -> bvn * bvn

val to_single_bits : bvn -> bvn list
