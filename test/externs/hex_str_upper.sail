default Order dec

$include <prelude.sail>

// Test for the hex_str_upper primitive
function main() -> unit = {
  assert(hex_str_upper(0) == "0x0");
  assert(hex_str_upper(255) == "0xFF");
  assert(hex_str_upper(-255) == "-0xFF");
  assert(hex_str_upper(18446744073709551616) == "0x10000000000000000");
}
