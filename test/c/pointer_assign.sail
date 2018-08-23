default Order dec

$include <vector_dec.sail>

register A : bits(32)
register B : bits(32)

let AB = [ref B, ref A]

let STATUS_1 = 0x0000_0002
let STATUS_2 = 0x0000_0004

val read_register = "reg_deref" : forall ('a : Type). register('a) -> 'a effect {rreg}

val or_bits = { c: "or_bits", _: "or_vec" } : forall 'n, 'n >= 0. (bits('n), bits('n)) -> bits('n)

overload operator | = {or_bits}

function main() : unit -> unit = {
  let C = AB[0];
  let c = read_register(C);
  print_bits("A = ", A);
  (*C) = c | STATUS_1;
  print_bits("A = ", A);
  (*(ref A)) = c | STATUS_2;
  print_bits("A = ", A);
}