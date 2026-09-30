default Order dec

$include <prelude.sail>

// Test for the lteq_int primitive
function main() -> unit = {
  assert(lteq_int(3, 5));
  assert(lteq_int(5, 5));
  assert(not_bool(lteq_int(6, 5)));
  assert(lteq_int(-18446744073709551616, 18446744073709551616));
}
