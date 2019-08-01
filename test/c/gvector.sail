default Order dec

$include <exception_basic.sail>
$include <vector_dec.sail>

val "print_int" : (string, int) -> unit

register R : vector(32, dec, bitvector(32, dec))

register T : vector(32, dec, int)

register Q : vector(3, dec, int)

val main : unit -> unit effect {rreg, wreg, escape}

function main () = {
  R[0] = 0xDEAD_BEEF;
  Q = [11435, 53414, 681];
  assert(Q[0] == 681);
  Q = [Q with 0 = 1000000];
  assert(Q[0] == 1000000);
  T[1] = 5;
  print_int("T[1] = ", T[1]);
  let y = T;
  print_int("y[1] = ", y[1]);
  print_bits("R[0] = ", R[0]);
}