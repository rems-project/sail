default Order dec
$include <prelude.sail>

// Two bitfield types with the same field names,
// testing the update functions of each

bitfield B1 : bits(32) = {
  Field0: (31..16 @ 7..0),
  Field1: 15..12,
}

bitfield B2 : bits(16) = {
  Field0: (15..12 @ 3..0),
  Field1: 7..4,
}

function main() -> unit = {
  b1 : B1 = Mk_B1(0x12345678);
  b2 : B2 = Mk_B2(0xabcd);
  assert(update_Field0(b1, 0xfedcba).bits == 0xfedc56ba);
  assert(update_Field0(b2, 0x12).bits == 0x1bc2);
  assert(update_Field1(b1, 0xf).bits == 0x1234f678);
  assert(update_Field1(b2, 0xf).bits == 0xabfd);
}
