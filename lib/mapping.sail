$ifndef _MAPPING
$define _MAPPING

mapping sep : string <-> unit = {
  forwards true <- __regex(", +") => (),
  backwards () => ", "
}

mapping spc : string <-> unit = {
  forwards true <- __regex(" +") => (),
  backwards () => " "
}

val "hex_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> string

$ifdef _DEFAULT_DEC
mapping hex forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- __parse_hex(n) => x,
  backwards x => hex_string(x)
}
$else
mapping hex forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, inc, bit) = {
  forwards x <- __parse_hex(n) => x,
  backwards x => hex_string(x)
}
$endif

val "binary_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> string

$ifdef _DEFAULT_DEC
mapping binary forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- __parse_binary(n) => x,
  backwards x => binary_string(x)
}
$else
mapping binary forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, inc, bit) = {
  forwards x <- __parse_binary(n) => x,
  backwards x => binary_string(x)
}
$endif

val "decimal_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> string

$ifdef _DEFAULT_DEC
mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- __parse_decimal(n) => x,
  backwards x => decimal_string(x)
}
$else
mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, inc, bit) = {
  forwards x <- __parse_decimal(n) => x,
  backwards x => decimal_string(x)
}
$endif

$ifdef _DEFAULT_DEC
mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- __parse_hex(n) => x,
  forwards x <- __parse_binary(n) => x,
  forwards x <- __parse_decimal(n) => x,
  backwards x => hex_string(x)
}
$else
mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- __parse_hex(n) => x,
  forwards x <- __parse_binary(n) => x,
  forwards x <- __parse_decimal(n) => x,
  backwards x => hex_string(x)
}
$endif

$endif
