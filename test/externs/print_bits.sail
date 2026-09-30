default Order dec

$include <prelude.sail>

// Test for the print_bits primitive
function main() -> unit = {
  print_bits("x = ", 0xAB);
  print_bits("y = ", 0b101);
  print_bits("", 0xFFFF_FFFF_FFFF_FFFF_F);
}
