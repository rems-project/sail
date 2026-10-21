default Order dec

$include <prelude.sail>

function f() -> unit = {
  var x : vector(2, bit) = [bitzero, bitzero];
  var y : bits(2) = 0b00;
  (x @ y) = 0b0000
}
