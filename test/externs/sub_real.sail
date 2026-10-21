default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the sub_real primitive
function main() -> unit = {
  assert(sub_real(5.5, 2.25) == 3.25);
  assert(sub_real(2.0, 2.0) == 0.0);
  assert(lt_real(sub_real(1.0, 2.0), 0.0));
}
