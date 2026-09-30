default Order dec

$include <prelude.sail>

// Test for the add_int primitive
function main() -> unit = {
  let x : int = 2;
  let y : int = 3;
  assert(add_int(x, y) == 5);
  assert(add_int(-7, 3) == -4);
  assert(add_int(18446744073709551615, 1) == 18446744073709551616);
  assert(add_int(-9223372036854775808, -1) == -9223372036854775809);
}
