default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
  let xs = 0xF @ 0xF;
  let xs = [ xs with 3 ..0 = 0xA ];
  print_bits("xs = ", xs);
  let xs = [ xs with 0 = bitone ];
  let xs = sail_zero_extend(xs[5 .. 0], 8);
  print_bits("xs = ", xs);
}
