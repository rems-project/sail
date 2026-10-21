default Order dec

$include <prelude.sail>

// Test for the prerr_endline primitive
function main() -> unit = {
  prerr_endline("hello");
  prerr_endline("");
  prerr_endline("world");
}
