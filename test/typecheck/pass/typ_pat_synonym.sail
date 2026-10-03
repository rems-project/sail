default Order dec

$include <prelude.sail>

type foo('n : Int) = vector('n, int)

function f(x : bits(4)) -> unit = match x {
  y as bits('n) => { let _ : int('n) = 4; () }
}

function g(x : foo(4)) -> unit = match x {
  y as foo('n) => { let _ : int('n) = 4; () }
}
