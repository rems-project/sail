default Order dec
$include <prelude.sail>

// A simple example where two different but equivalent unifiers will be found
// for the parameter of f, and the type checker just needs to notice that they're
// equivalent and pick one.

struct Foo ('m, 'n) = {
  a: int('m),
  b: int('n),
}

val f : forall 'n. Foo('n,'n) -> int
function f(x) = x.a
val g : forall 'm 'n, 'm == 'n. Foo('m,'n) -> int
function g(x) = f(x)
