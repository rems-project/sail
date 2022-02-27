default Order dec

$include <prelude.sail>

let b: bool = true

val test : int -> int

function test(x) = {
  if b then {
    return x + 1;
    ()
  } else {
    ()
  };
  z: int = x + 1;
  z
}

let x: int = {
  var y: int = 3;
  y = test(y);
  y
}
