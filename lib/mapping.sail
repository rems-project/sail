$ifndef _MAPPING
$define _MAPPING

mapping sep : regex(", +") <-> unit = {
  forwards str <- regex(", +") => (),
  backwards () => ", "
}

mapping spc : regex(" +") <-> unit = {
  forwards str <- regex(" +") => (),
  backwards () => " "
}

val "hex_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> regex("0x[0-9a-f]+")

val "hex_parse" : forall 'n ('ord : Order), 'n >= 0. string -> vector('n, 'ord, bit)

$ifdef _DEFAULT_DEC
mapping hex forall 'n, 'n >= 0. (n: int('n)) -> regex("0x[0-9a-f]+") <-> vector('n, dec, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  backwards x => hex_string(x)
}
$else
mapping hex forall 'n, 'n >= 0. (n: int('n)) -> regex("0x[0-9a-f]+") <-> vector('n, inc, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  backwards x => hex_string(x)
}
$endif

val "binary_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> regex("0b[0-1]+")

val "binary_parse" : forall 'n ('ord : Order), 'n >= 0. string -> vector('n, 'ord, bit)

$ifdef _DEFAULT_DEC
mapping binary forall 'n, 'n >= 0. (n: int('n)) -> regex("0b[0-1]+") <-> vector('n, dec, bit) = {
  forwards x <- regex("0b[0-1]+") => binary_parse(x),
  backwards x => binary_string(x)
}
$else
mapping binary forall 'n, 'n >= 0. (n: int('n)) -> regex("0b[0-1]+") <-> vector('n, inc, bit) = {
  forwards x <- regex("0b[0-1]+") => binary_parse(x),
  backwards x => binary_string(x)
}
$endif

val "decimal_string" : forall 'n ('ord : Order), 'n >= 0. vector('n, 'ord, bit) -> regex("[1-9][0-9]*")

val "decimal_parse" : forall 'n ('ord : Order), 'n >= 0. string -> vector('n, 'ord, bit)

$ifdef _DEFAULT_DEC
mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> regex("[1-9][0-9]*") <-> vector('n, dec, bit) = {
  forwards x <- regex("[1-9][0-9]*") => decimal_parse(x),
  backwards x => decimal_string(x)
}
$else
mapping decimal forall 'n, 'n >= 0. (n: int('n)) -> regex("[1-9][0-9]*") <-> vector('n, inc, bit) = {
  forwards x <- regex("[1-9][0-9]*") => decimal_parse(x),
  backwards x => decimal_string(x)
}
$endif

$ifdef _DEFAULT_DEC
mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  forwards x <- regex("0b[0-1]+")    => binary_parse(x),
  forwards x <- regex("[1-9][1-9]*") => decimal_parse(x),
  backwards x => hex_string(x)
}
$else
mapping bits forall 'n, 'n >= 0. (n: int('n)) -> string <-> vector('n, dec, bit) = {
  forwards x <- regex("0x[0-9a-f]+") => hex_parse(x),
  forwards x <- regex("0b[0-1]+")    => binary_parse(x),
  forwards x <- regex("[1-9][1-9]*") => decimal_parse(x),
  backwards x => hex_string(x)
}
$endif

$endif
