default Order dec

$include <prelude.sail>

val f : forall 'b. int('b) -> unit

function f(b) = {
  let 'a = 3;
  if b == 3 then {
     let _ : bool('a == 'b) = true;
  }
}

function g forall 'b. (b: bool('b)) -> unit = {
  ()
}
