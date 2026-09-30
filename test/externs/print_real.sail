default Order dec

$include <prelude.sail>
$include <real.sail>

// Test for the print_real primitive
function main() -> unit = {
  print_real("x = ", 2.5);
  print_real("y = ", 1.0);
}
