default Order dec

$include <arith.sail>
$include <vector_dec.sail>

val "zeros" : forall 'n. int('n) -> bits('n)

val main : unit -> unit

function main() = {
  let x = [0x1FFFF0000FFFF0000 with 15 .. 0 = 0xFFFF];
  print_bits("x = ", x);
  print_int("length(x) = ", length(x));
  let y = replicate_bits(x, 3);
  print_bits("y = ", y);
  print_int("length(y) = ", length(y));
  let z = [y with 63 .. (63 - 15) = 0xCAFE];
  print_bits("z = ", z);
  print_int("length(z) = ", length(z));
  q = slice(z, 0, 64 * 3);
  print_bits("q = ", q);
  w = signed(q);
  print_int("w = ", w);
  print_int("length(q) = ", length(q));
  print_bits("", [0xFFFF with 14 .. 0 = zeros(15)]);
  print_bits("0b1 @ zeros(64 * 3 - 1) = ", 0b1 @ zeros(64 * 3 - 1));
  q[64 * 3 - 2 .. 0] = zeros(64 * 3 - 1);
  print_bits("q                       = ", q);
  ()
}
