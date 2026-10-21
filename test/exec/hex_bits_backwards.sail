default Order dec
$include <prelude.sail>
$include <hex_bits.sail>
$include <hex_bits_signed.sail>

/* The sized hex_bits mappings used to have unconditional patterns in the backwards direction, which
   caused failures if they were used as part of a larger mapping. */

val test_map : bits(12) <-> string

scattered mapping test_map
mapping clause test_map = bs <-> hex_bits_12(bs)
mapping clause test_map = 0x123 <-> "hello"
end test_map

val test_map_signed : bits(12) <-> string

scattered mapping test_map_signed
mapping clause test_map_signed = bs <-> hex_bits_signed_12(bs)
mapping clause test_map_signed = 0x123 <-> "hello"
end test_map_signed

function main() -> unit = {
  assert(test_map("hello") == 0x123);
  assert(test_map("0x123") == 0x123);
  assert(test_map("0x456") == 0x456);
  assert(test_map(0x123) == "0x123");
  assert(test_map(0x456) == "0x456");

  assert(test_map_signed("hello") == 0x123);
  assert(test_map_signed("0x123") == 0x123);
  assert(test_map_signed("0x456") == 0x456);
  assert(test_map_signed(0x123) == "0x123");
  assert(test_map_signed(0x456) == "0x456");
}
