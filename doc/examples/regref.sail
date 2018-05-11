default Order dec
$include <prelude.sail>

register X0 : bits(8)
register X1 : bits(8)
register X2 : bits(8)

let X : vector(3, dec, register(bits(8))) = [ref X2, ref X1, ref X0]

function main() : unit -> unit = {
  X0 = 0xFF;
  assert(X0 == 0xFF);
  (*X[0]) = 0x11;
  assert(X0 == 0x11);
  (*ref X0) = 0x00;
  assert(X0 == 0x00)
}