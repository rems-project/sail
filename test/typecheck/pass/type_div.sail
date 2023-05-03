default Order dec
$include <prelude.sail>

// At the function call f(x) the type checker will need to unify (8 * 'n) and 'm for 'n.
// The support during unification for division can solve it with 'n => div('m, 8).

val f : forall 'n. int(8 * 'n) -> int
function f(x) = x

val g : forall 'm 'p, 'm == 8 * 'p. int('m) -> int
function g(x) = f(x)
