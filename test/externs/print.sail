default Order dec

$include <prelude.sail>

// Test for the print primitive
function main() -> unit = {
  print("hello");
  print(" ");
  print("world\n");
}
