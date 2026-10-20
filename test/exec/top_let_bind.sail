default Order dec
$include <prelude.sail>

function f(b : bool) -> int = {
  assert(b);
  10
}

let v1 = 1 + f(true)
let v2 = let x : int = f(true) in 1 + x

function main() -> unit = {
  assert(v1 == 11);
  assert(v2 == 11);
}
