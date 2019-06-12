$ifndef _MAPPING
$define _MAPPING

$include <string.sail>

mapping sep : regex(", +") <-> unit = {
  forwards _ <- regex(", +") => (),
  backwards () => ", "
}

mapping spc : regex(" +") <-> unit = {
  forwards _ <- regex(" +") => (),
  backwards () => " "
}

val "hex_string" : forall 'n, 'n >= 0. vector('n, dec, bit) -> regex("0x[0-9a-f]+")

val "hex_parse" : forall 'n, 'n >= 0. string -> vector('n, dec, bit)

mapping hex forall 'n, 'n >= 0. (n: int('n)) -> regex("0x[0-9a-f]+") <-> vector('n, dec, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  backwards x => hex_string(x)
}

val "binary_string" : forall 'n, 'n >= 0. vector('n, dec, bit) -> regex("0b[0-1]+")

val "binary_parse" : forall 'n, 'n >= 0. string -> vector('n, dec, bit)

mapping binary forall 'n, 'n >= 0. (n: int('n)) -> regex("0b[0-1]+") <-> vector('n, dec, bit) = {
  forwards x <- regex("0b[0-1]+") => binary_parse(x),
  backwards x => binary_string(x)
}

val "decimal_string" : forall 'n, 'n >= 0. vector('n, dec, bit) -> regex("[1-9][0-9]*")

val "decimal_parse" : forall 'n, 'n >= 0. string -> vector('n, dec, bit)

mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> regex("[1-9][0-9]*") <-> vector('n, dec, bit) = {
  forwards x <- regex("[1-9][0-9]*") => decimal_parse(x),
  backwards x => decimal_string(x)
}

mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  forwards x <- regex("0b[0-1]+")    => binary_parse(x),
  forwards x <- regex("[1-9][1-9]*") => decimal_parse(x),
  backwards x => hex_string(x)
}

$endif
