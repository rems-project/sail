default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the abs_real primitive
function main() -> unit = {
  assert(abs_real(2.5) == 2.5);
  assert(abs_real(sub_real(0.0, 2.5)) == 2.5);
  assert(abs_real(0.0) == 0.0);
}
