open Ast
open Bit
open Datatypes
open List0
open ListDef

val same_bits : bit list -> bit list -> bool

val of_hex_digit : hex_digit -> bit list

val hex_digit_of_nibble : bit -> bit -> bit -> bit -> hex_digit

val to_hex_digits : bit list -> hex_digit list option

val non_empty_to_list : 'a1 non_empty -> 'a1 list

val of_hex_lit : hex_digit non_empty list -> bit list

val of_bin_lit : bin_digit non_empty list -> bit list

val to_gvector : value -> value
