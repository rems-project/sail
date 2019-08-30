default Order dec

$include <prelude.sail>

val f : (int, int) -> int
val g : (int, int) -> int

function f(x,y) = {
  if x == 0 then 0 else
  if x < 0 then -1 else g(y,x - 1)
}

function g(y,x) = {
  if x == 0 then 0 else
  if x < 0 then -1 else f(x - 1,y)
}

termination_measure f(x,y) = abs_int(x)
termination_measure g(x,y) = abs_int(y)

val test : int -> bool

function test(x) = f(x,4) == g(5,x)
