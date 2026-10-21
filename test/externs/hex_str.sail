default Order dec

$include <prelude.sail>

// Test for the hex_str primitive
function main() -> unit = {
  assert(hex_str(0) == "0x0");
  assert(hex_str(255) == "0xff");
  assert(hex_str(-255) == "-0xff");
  assert(hex_str(18446744073709551616) == "0x10000000000000000");
}
