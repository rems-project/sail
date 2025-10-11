default Order dec

$include <prelude.sail>

enum word_width = BYTE | HALF | WORD | DOUBLE

val size_bits : word_width <-> bits(2)

mapping size_bits = {
  BYTE   <-> 0b00,
  HALF   <-> 0b01,
  WORD   <-> 0b10,
  DOUBLE <-> 0b11
}

mapping size_bits2 : word_width <-> bits(2) = {
  BYTE   <-> 0b00,
  HALF   <-> 0b01,
  WORD   <-> 0b10,
  DOUBLE <-> 0b11
}

mapping size_bits3 : word_width <-> bits(2) = {
  BYTE <-> 0b00,
  HALF <-> 0b01,
  WORD <-> 0b10,
  forwards  DOUBLE => 0b11, // forwards is left-to-right
  backwards 0b11 => DOUBLE, // backwards is right-to-left
}

mapping ta_flag : string <-> bits(1) = {
  "ta" <-> 0b1,
  "tu" <-> 0b0,
}

$[sv_function { types = "int #0" }]
val "parse_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bits('n)

$[sv_function { types = "int #0" }]
val "valid_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bool

val hex_bits : forall 'n, 'n > 0. bits('n) <-> (int('n), string)

function hex_bits_forwards(bv) = (length(bv), hex_str(unsigned(bv)))
function hex_bits_forwards_matches(bv) = true

function hex_bits_backwards(n, str) = parse_hex_bits(n, str)
function hex_bits_backwards_matches(n, str) = valid_hex_bits(n, str)

mapping hex_bits_2 : bits(2) <-> string = { hex_bits(2, s) <-> s }

val string_append = pure {
  coq: "String.append",
  lean: "String.append",
  c: "concat_str",
  cpp: "concat_str",
  _: "string_append"
} : (string, string) -> string

mapping vtype_assembly : string <-> (bits(1), bits(1)) = {
  ta_flag(sew) ^ ta_flag(ta) <-> (ta, sew) when eq_bit(sew[0], bitone),
  hex_bits_2(ta @ sew)  <-> (ta, sew),
}

mapping vtype_assembly2 : string <-> (bits(1), bits(1)) = {
  hex_bits_2(ta @ sew)  <-> (ta, sew),
}

mapping vtype_assembly3 : string <-> (bits(1), bits(1)) = {
  ta_flag(sew) ^ ta_flag(ta) <-> (ta, sew),
}
