default Order dec

$include <prelude.sail>

////////////////////////////////////////////////////////////

val works : bits(8) -> bits(3)
function works bv = match bv {
  a : bits(3) @ b : bits(2) @ 0b000 => a
}

val doesnt : bits(8) -> bits(3)
function doesnt bv = match bv {
  (a : bits(3) @ b : bits(2)) @ 0b000 => a
}

val "print_bits" : forall 'n. (string, bits('n)) -> unit

val main : unit -> unit

function main() = {
  print_bits("works = ", works(0b1010_0000));
  print_bits("doesnt = ", doesnt(0b0101_0000));
}