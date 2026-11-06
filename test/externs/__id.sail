default Order dec

$include <prelude.sail>

// Test for the __id primitive
function main() -> unit = {
  assert(__id(42) == 42);
  assert(__id(-42) == -42);
  assert(__id(18446744073709551616) == 18446744073709551616);
}
