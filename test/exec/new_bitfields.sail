default Order dec

$include <prelude.sail>

bitfield B : bits(32) = {
  Field0: (31..16 @ 7..0),
  Field1: 15..8
}

register R : B

function main() -> unit = {
  R[Field1] = 0x00;
  R[Field0] = 0x4711FF;
  assert(R[Field1] == 0x00);
  assert(R[Field0] == 0x4711FF);
  print_bits("R.bits=", R.bits);
  assert(R.bits == 0x471100FF);
  R = [R with Field0 = 0xFF0077];
  assert(R[Field1] == 0x00);
  assert(R[Field0] == 0xFF0077);
  print_bits("R.bits=", R.bits);
  assert(R.bits == 0xFF000077);
  R = [R with Field1 = 0x47, Field0 = 0x000011];
  assert(R[Field1] == 0x47);
  assert(R[Field0] == 0x000011);
  print_bits("R.bits=", R.bits);
  assert(R.bits == 0x00004711)
}
