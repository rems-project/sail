
default Order dec

val "print_bits" : forall 'n. (string, vector('n, dec, bit)) -> unit

val main : unit -> unit

function main () = {
  let x : bit = bitone;
  let y : vector(4, dec, bit) = [x, bitone, bitzero, x];
  print_bits("y = ", y);
}