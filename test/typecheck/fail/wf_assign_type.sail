default Order dec

$include <prelude.sail>

type bar : Int = 10

function foo() -> bits(bar) = {
  let X = sizeof(bar);
  var Y : bits(X) = 0b00;
  Y
}
