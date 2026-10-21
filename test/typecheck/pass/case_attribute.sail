default Order dec
$include <prelude.sail>

function f(x : int) -> int = match x {
  $[foo] (1 => 2),
  _ => 3
}
