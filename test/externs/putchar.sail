default Order dec

$include <prelude.sail>
$include <asl_compat.sail>

// Test for the putchar primitive
function main() -> unit = {
  putchar(72);
  putchar(105);
  putchar(10);
}
