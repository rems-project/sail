default Order dec

$include <prelude.sail>

// Test for the print_int primitive
function main() -> unit = {
  print_int("x = ", 42);
  print_int("y = ", -3);
  print_int("", 0);
  print_int("big = ", 18446744073709551616);
}
