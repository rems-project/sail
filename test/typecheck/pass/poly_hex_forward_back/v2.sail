default Order dec

$include <prelude.sail>

val hex_bits : forall 'n, 'n >= 0. implicit('n) -> string <-> bits('n)

val sep : string <-> unit

val any_string : string <-> unit

val string_of_hex : forall 'n, 'n >= 0. bits('n) -> string

infixr 1 ^^
val operator ^^ : (string, string) -> string

val hex_twice : forall 'n, 'n >= 0. int('n) -> option((bits('n), bits('n)))

mapping hex_twice(n) = {
  forwards x <- hex_bits(n) ^ sep() ^ y <- hex_bits(n) => Some(x, y),
  backwards Some(x, y) => string_of_hex(x) ^^ ", " ^^ string_of_hex(y),
  any_string() <-> None()
}
