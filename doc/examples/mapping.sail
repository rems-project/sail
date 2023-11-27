default Order dec
$include <prelude.sail>

enum word_width = {BYTE, HALF, WORD, DOUBLE}

val size_bits : word_width <-> bits(2)

$span start M1
mapping size_bits = {
  BYTE   <-> 0b00,
  HALF   <-> 0b01,
  WORD   <-> 0b10,
  DOUBLE <-> 0b11
}
$span end

$span start M2
mapping size_bits2 : word_width <-> bits(2) = {
  BYTE   <-> 0b00,
  HALF   <-> 0b01,
  WORD   <-> 0b10,
  DOUBLE <-> 0b11
}
$span end

function example() -> unit = {
  let width : word_width = size_bits(0b00);
  let width : bits(2) = size_bits(BYTE);
}

$span start M3
mapping size_bits3 : word_width <-> bits(2) = {
  BYTE <-> 0b00,
  HALF <-> 0b01,
  WORD <-> 0b10,
  forwards  DOUBLE => 0b11, // forwards is left-to-right
  backwards 0b11 => DOUBLE, // backwards is right-to-left
}
$span end
