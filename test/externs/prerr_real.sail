default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the prerr_real primitive
function main() -> unit = {
  prerr_real("x = ", 2.5);
  prerr_real("y = ", 1.0);
}
