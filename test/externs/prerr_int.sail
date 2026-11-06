default Order dec

$include <prelude.sail>

// Test for the prerr_int primitive
function main() -> unit = {
  prerr_int("x = ", 42);
  prerr_int("y = ", -3);
  prerr_int("big = ", 18446744073709551616);
}
