$ifndef _REVERSE_MAPPING
$define _REVERSE_MAPPING

$include <string.sail>

mapping sep : unit <-> regex(", *") = {
  backwards _ <- regex(", *") => (),
  forwards () => ", "
}

mapping spc : unit <-> regex(" +") = {
  backwards _ <- regex(" +") => (),
  forwards () => " "
}

val "hex_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("0x[0-9a-f]+")

val "hex_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping hex forall 'n, 'n >= 0. (n: int('n)) -> bitvector('n, dec) <-> regex("0x[0-9a-f]+") = {
  backwards x <- regex("0x[0-9a-f]+") => hex_parse(n, x),
  forwards x => hex_string(x)
}

mapping opt_spc : unit <-> regex(" *") = {
  backwards _ <- regex(" *") => (),
  forwards () => ""
}

val "binary_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("0b[0-1]+")

val "binary_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping binary forall 'n, 'n >= 0. (n: int('n)) -> bitvector('n, dec) <-> regex("0b[0-1]+") = {
  backwards x <- regex("0b[0-1]+") => binary_parse(n, x),
  forwards x => binary_string(x)
}

val "decimal_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> regex("[0-9]+")

val "decimal_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> bitvector('n, dec) <-> regex("[0-9]+") = {
  backwards x <- regex("[0-9]+") => decimal_parse(n, x),
  forwards x => decimal_string(x)
}

mapping bits forall 'n, 'n >= 0. (n: int('n)) -> bitvector('n, dec) <-> string = {
  backwards x <- regex("0x[0-9a-f]+") => hex_parse(n, x),
  backwards x <- regex("0b[0-1]+")    => binary_parse(n, x),
  backwards x <- regex("[0-9]+") => decimal_parse(n, x),
  forwards x => hex_string(x)
}

$endif
