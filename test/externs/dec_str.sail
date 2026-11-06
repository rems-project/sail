default Order dec

$include <prelude.sail>

// Test for the dec_str primitive
function main() -> unit = {
  assert(dec_str(0) == "0");
  assert(dec_str(42) == "42");
  assert(dec_str(-42) == "-42");
  assert(dec_str(18446744073709551616) == "18446744073709551616");
}
