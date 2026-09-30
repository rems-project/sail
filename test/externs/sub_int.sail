default Order dec

$include <prelude.sail>

// Test for the sub_int primitive
function main() -> unit = {
  let x : int = 5;
  let y : int = 3;
  assert(sub_int(x, y) == 2);
  assert(sub_int(y, x) == -2);
  assert(sub_int(18446744073709551616, 1) == 18446744073709551615);
  assert(sub_int(-9223372036854775808, 1) == -9223372036854775809);
}
