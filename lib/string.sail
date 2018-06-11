$ifndef _STRING
$define _STRING

$include <arith.sail>

val eq_string = {lem: "eq", _: "eq_string"} : (string, string) -> bool

infixl 9 ^-^

val concat_str = {lem: "stringAppend", _: "concat_str"} : (string, string) -> string

val "dec_str" : int -> string

val "hex_str" : int -> string

val bits_str = "string_of_bits" : forall 'n. vector('n, dec, bit) -> string

val concat_str_bits : forall 'n. (string, vector('n, dec, bit)) -> string

function concat_str_bits(str, x) = concat_str(str, bits_str(x))

val concat_str_dec : (string, int) -> string

function concat_str_dec(str, x) = concat_str(str, dec_str(x))

overload operator ^-^ = {concat_str, concat_str_bits, concat_str_dec}

val print_endline = "print_endline" : string -> unit

val prerr_endline = "prerr_endline" : string -> unit

$endif
