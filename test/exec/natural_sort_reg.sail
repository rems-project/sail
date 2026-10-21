default Order dec

$include <prelude.sail>

register R1 : bits(32) = 0x0000_0001
register R10 : bits(32) = 0x0000_0002
register R2 : bits(32) = 0x0000_0003

val main : unit -> unit

function main() = {
  print_bits("R1 = ", R1);
  print_bits("R10 = ", R10);
  print_bits("R2 = ", R2);
  let r = ref R10;
  print_bits("*r = ", *r);
  *r = 0x0000_0004;
  print_bits("*r = ", *r);
}
