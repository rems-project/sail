default Order dec

$include <prelude.sail>

$option -new_bitfields

bitfield B : bits(32) = {
  Field: 7..0
}

register R : B

function main() -> unit = {
  R[Field] = 0xFF;
  assert(R[Field] == 0xFF)
}