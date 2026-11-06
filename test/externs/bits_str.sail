default Order dec

$include <prelude.sail>

// Test for the bits_str primitive
function main() -> unit = {
  // Bitvectors whose length is a multiple of four are shown in hex
  assert(bits_str(0xAB) == "0xAB");
  assert(bits_str(0x0) == "0x0");
  assert(bits_str(0b101) == "0b101");
  assert(bits_str(0xFFFF_FFFF_FFFF_FFFF_F) == "0xFFFFFFFFFFFFFFFFF");
}
