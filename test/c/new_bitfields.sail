default Order dec

$include <prelude.sail>

bitfield B : bits(32) = {
  Field1: 15..8,
  Field0: 7..0
}

register R : B

function main() -> unit = {
  R[Field1] = 0x00;
  R[Field0] = 0xFF;
  assert(R[Field1] == 0x00);
  assert(R[Field0] == 0xFF);
  print_bits("R.bits=", R.bits);
  R = [R with Field0 = 0x77];
  assert(R[Field1] == 0x00);
  assert(R[Field0] == 0x77);
  print_bits("R.bits=", R.bits);
  R = [R with Field1 = 0x47, Field0 = 0x11];
  assert(R[Field1] == 0x47);
  assert(R[Field0] == 0x11);
  print_bits("R.bits=", R.bits)
}
