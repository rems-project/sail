default Order dec

$include <prelude.sail>

// Test for the prerr_bits primitive
function main() -> unit = {
  prerr_bits("x = ", 0xAB);
  prerr_bits("y = ", 0b101);
}
