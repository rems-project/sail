$ifndef _MAPPING
$define _MAPPING

$include <string.sail>

val "string_match" : (string, string) -> bool

mapping sep : token(", *") <-> unit = {
  forwards x if string_match(", *", x) => (),
  backwards () => ", "
}

mapping spc : token(" +") <-> unit = {
  forwards x if string_match(" +", x) => (),
  backwards () => " "
}

mapping hash : token("#") <-> unit = {
  forwards x if string_match("#", x) => (),
  backwards () => "#"
}

val "hex_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> token("0x[0-9a-f]+")

val "hex_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping hex forall 'n, 'n >= 0. (n: int('n)) -> token("0x[0-9a-f]+") <-> bitvector('n, dec) = {
  forwards x if string_match("0x[0-9a-f]+", x) => hex_parse(n, x),
  backwards x => hex_string(x)
}

mapping opt_spc : token(" *") <-> unit = {
  forwards x if string_match(" *", x) => (),
  backwards () => ""
}

val "binary_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> token("0b[0-1]+")

val "binary_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping binary forall 'n, 'n >= 0. (n: int('n)) -> token("0b[0-1]+") <-> bitvector('n, dec) = {
  forwards x if string_match("0b[0-1]+", x) => binary_parse(n, x),
  backwards x => binary_string(x)
}

val "decimal_string" : forall 'n, 'n >= 0. bitvector('n, dec) -> token("[0-9]+")

val "decimal_parse" : forall 'n, 'n >= 0. (int('n), string) -> bitvector('n, dec)

mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> token("[0-9]+") <-> bitvector('n, dec) = {
  forwards x if string_match("[0-9]+", x) => decimal_parse(n, x),
  backwards x => decimal_string(x)
}

mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> bitvector('n, dec) = {
  forwards x if string_match("0x[0-9a-f]+", x) => hex_parse(n, x),
  forwards x if string_match("0b[0-1]+", x)    => binary_parse(n, x),
  forwards x if string_match("[0-9]+", x)      => decimal_parse(n, x),
  backwards x => hex_string(x)
}

mapping option_bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> option(bitvector('n, dec)) = {
  forwards x if string_match("0x[0-9a-f]+", x) => Some(hex_parse(n, x)),
  forwards x if string_match("0b[0-1]+", x)    => Some(binary_parse(n, x)),
  forwards x if string_match("[0-9]+", x)      => Some(decimal_parse(n, x)),
  forwards _                                   => None(),
  backwards Some(x) => hex_string(x)
}

/* __split and __group are used to re-write string append patterns */

val __split = {
  _: "__split"
} : (string, string, int) -> __match

val __matched = {
  _: "__matched"
} : __match -> bool

val __group = {
  _: "__group"
} : (int, __match) -> string

$endif
