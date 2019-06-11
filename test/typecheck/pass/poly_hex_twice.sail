default Order dec

$include <prelude.sail>
$include <string.sail>

val hex_bits : forall 'n, 'n >= 0. implicit('n) -> string <-> bits('n)

val sep : string <-> unit

val any_string : string <-> unit

val hex_twice : forall 'n, 'n >= 0. int('n) -> string <-> option((bits('n), bits('n)))

mapping hex_twice forall 'n, 'n >= 0. (n: int('n)) -> string <-> option((bits('n), bits('n))) = {
  x <- hex_bits(n) ^ sep() ^ y <- hex_bits(n) <-> Some(x, y),
  any_string() <-> None()
}
