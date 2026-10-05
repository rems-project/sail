default Order dec

$include <prelude.sail>

function f() -> unit = {
  var x : bits(2) = 0b00;
  var y : vector(2, bit) = [bitzero, bitzero];
  (x @ y) = 0b0000
}
