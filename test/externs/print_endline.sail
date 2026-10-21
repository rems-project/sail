default Order dec

$include <prelude.sail>

// Test for the print_endline primitive
function main() -> unit = {
  print_endline("hello");
  print_endline("");
  print_endline("world");
}
