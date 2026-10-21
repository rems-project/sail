default Order dec

$include <prelude.sail>

function f(x : int) -> unit = match x {
  [|y|] => (),
  _ => ()
}
