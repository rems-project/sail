default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the lt_real primitive
function main() -> unit = {
  assert(lt_real(1.5, 2.5));
  assert(not_bool(lt_real(2.5, 2.5)));
  assert(not_bool(lt_real(3.5, 2.5)));
}
