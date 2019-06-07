default Order dec

$include <prelude.sail>

val hex_bits : forall 'n, 'n >= 0. implicit('n) -> string <-> bits('n)

val sep : string <-> unit

val any_string : string <-> unit

val hex_twice : forall 'n, 'n >= 0. int('n) -> string <-> option((bits('n), bits('n)))

val string_of_hex : forall 'n, 'n >= 0. bits('n) -> string

infixr 1 ^^
val operator ^^ : (string, string) -> string

mapping hex_twice forall 'n, 'n >= 0. (n: int('n)) -> string <-> option((bits('n), bits('n))) = {
  forwards x <- hex_bits(n) ^ sep() ^ y <- hex_bits(n) --> Some(x, y),
  backwards string_of_hex(x) ^^ ", " ^^ string_of_hex(y) <-- Some(x, y),
  any_string() <-> None()
}
