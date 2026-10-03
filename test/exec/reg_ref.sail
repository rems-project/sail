default Order dec
$include <prelude.sail>

register X : bits(64)

val main : unit -> unit

function main() = {
  let reg = ref X;
  (*reg) = 0xFFFF_FFFF_FFFF_FFFF;
  print_bits("X = ", *reg);
  (*reg) = 0xFFFF_0000_FFFF_ABCD;
  print_bits("X = ", *reg);
}
