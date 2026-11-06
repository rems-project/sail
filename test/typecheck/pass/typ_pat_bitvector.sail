default Order dec

$include <prelude.sail>

function f(x : bits(4)) -> unit = match x {
  y as bitvector('n) => { let _ : int('n) = 4; () }
}
