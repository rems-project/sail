default Order dec

$include <prelude.sail>
$include <exception_basic.sail>

enum pred = {
  P_false,
  P_true
}

mapping decenc_p : pred <-> bits(2) = {
  P_true <-> 0b00,
  P_false <-> 0b01
}

scattered union ast

val encdec : ast <-> bits(16)

union clause ast = ABS : (pred, bits(10))

mapping clause encdec =
      ABS((0b0 @ p : bits(1)) <- decenc_p(), rd : bits(5) @ rs : bits(5))
  <-> 0b10011 @ p : bits(1) @ rd : bits(5) @ rs : bits(5)

function fetch(_: unit) -> bits(16) = {
  0b10011 @ 0xFF @ 0b111
}

val main : unit -> unit effect {barr, eamem, escape, exmem, rmem, rreg, wmv, wreg}
function main () = {
  let bin = fetch();
  let ast = encdec(bin);
  let bin' = encdec(ast);
  assert(bin == bin');
  print_bits("bin = ", bin);
  print_bits("bin' = ", bin')
}
