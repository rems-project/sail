default Order dec

$include <prelude.sail>

val foo : forall ('n : Int) ('b : Bool).
  (bool('b), int('n)) -> {'m, 'b & 'm == 'n | not('b) & 'm == 3. int('m)}

function foo(b, n) = {
  if b then n else 3
}