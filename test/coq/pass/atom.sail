default Order dec
$include <flow.sail>
$include <arith.sail>

val f : forall 'n, 'n >= 0. atom(8 * 'n) -> int

function f(x) = x+1

val g : forall 'n, 'n > 0. atom('n) -> atom(2*'n)
val h : forall 'n, 'n > 1. atom('n) -> int

function h(x) = x

val test : unit -> bool

function test() = {
  /* Using f with Coq would need us to provide/infer witnesses for 'n
  f(0) == 1 & f(8) == 9
  */
  h(g(1)) == 2
}