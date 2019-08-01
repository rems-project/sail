
default Order dec

val "print_bits" : forall 'n. (string, bitvector('n, dec)) -> unit

val main : unit -> unit

function main () = {
  let x : bit = bitone;
  let y : bitvector(4, dec) = [x, bitone, bitzero, x];
  print_bits("y = ", y);
}