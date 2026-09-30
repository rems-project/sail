default Order dec

$include <prelude.sail>

// Test for the mult_int primitive
function main() -> unit = {
  let x : int = 6;
  let y : int = 7;
  assert(mult_int(x, y) == 42);
  assert(mult_int(-6, 7) == -42);
  assert(mult_int(-6, -7) == 42);
  assert(mult_int(4294967296, 4294967296) == 18446744073709551616);
}
