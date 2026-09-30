default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the gteq_real primitive
function main() -> unit = {
  assert(gteq_real(2.5, 1.5));
  assert(gteq_real(2.5, 2.5));
  assert(not_bool(gteq_real(1.5, 2.5)));
}
