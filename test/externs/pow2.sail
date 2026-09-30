default Order dec

$include <prelude.sail>

// Test for the pow2 primitive
function main() -> unit = {
  assert(pow2(0) == 1);
  assert(pow2(1) == 2);
  assert(pow2(10) == 1024);
  assert(pow2(64) == 18446744073709551616);
}
