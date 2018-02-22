default Order dec

$include <vector_dec.sail>

val "print_int" : (string, int) -> unit

register R : vector(32, dec, vector(32, dec, bit))

register T : vector(32, dec, int)

val main : unit -> unit effect {rreg, wreg}

function main () = {
  R[0] = 0xDEAD_BEEF;
  T[1] = 5;
  print_int("T[1] = ", T[1]);
  let y = T;
  print_int("y[1] = ", y[1]);
  print_bits("R[0] = ", R[0]);
}