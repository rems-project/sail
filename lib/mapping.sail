$ifndef _MAPPING
$define _MAPPING

$include <string.sail>

mapping sep : regex(", *") <-> unit = {
  forwards _ <- regex(", *") => (),
  backwards () => ", "
}

mapping spc : regex(" +") <-> unit = {
  forwards _ <- regex(" +") => (),
  backwards () => " "
}

mapping hash : regex("#") <-> unit = {
  forwards _ <- regex("#") => (),
  backwards () => "#"
}

val "hex_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("0x[0-9a-f]+")

val "hex_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping hex forall 'n, 'n >= 0. (n: int('n)) -> regex("0x[0-9a-f]+") <-> bitvector('n, dec) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(n, x),
  backwards x => hex_string(x)
}

mapping opt_spc : regex(" *") <-> unit = {
  forwards _ <- regex(" *") => (),
  backwards () => ""
}

val "binary_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("0b[0-1]+")

val "binary_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping binary forall 'n, 'n >= 0. (n: int('n)) -> regex("0b[0-1]+") <-> bitvector('n, dec) = {
  forwards x <- regex("0b[0-1]+") => binary_parse(n, x),
  backwards x => binary_string(x)
}

val "decimal_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("[0-9]+")

val "decimal_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> regex("[0-9]+") <-> bitvector('n, dec) = {
  forwards x <- regex("[0-9]+") => decimal_parse(n, x),
  backwards x => decimal_string(x)
}

mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> bitvector('n, dec) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(n, x),
  forwards x <- regex("0b[0-1]+")    => binary_parse(n, x),
  forwards x <- regex("[0-9]+")      => decimal_parse(n, x),
  backwards x => hex_string(x)
}

mapping option_bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> option(bitvector('n, dec)) = {
  forwards x <- regex("0x[0-9a-f]+") => Some(hex_parse(n, x)),
  forwards x <- regex("0b[0-1]+")    => Some(binary_parse(n, x)),
  forwards x <- regex("[0-9]+")      => Some(decimal_parse(n, x)),
  forwards _                         => None(),
  backwards Some(x) => hex_string(x)
}

val __split = {
  _: "__split"
} : (string, string) -> (bool, __match)

val __group = {
  _: "__group"
} : (int, __match) -> string

$endif
