default Order dec

$include <prelude.sail>

// Test for the prerr primitive
function main() -> unit = {
  prerr("hello");
  prerr(" ");
  prerr("world\n");
}
