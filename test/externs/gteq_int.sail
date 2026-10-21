default Order dec

$include <prelude.sail>

// Test for the gteq_int primitive
function main() -> unit = {
  assert(gteq_int(5, 3));
  assert(gteq_int(5, 5));
  assert(not_bool(gteq_int(5, 6)));
  assert(gteq_int(18446744073709551616, -18446744073709551616));
}
