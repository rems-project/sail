default Order dec
$include <prelude.sail>

/* In the let x = ... the x will get an existential type, and we need
   to take care not to accidentally cast it because the type variable
   doesn't match the original.

   Also incidentally tests that we can generate an initial value for a
   type with a range inside.
 */

struct Params = {
  size : {2,4},
}

union Foo ('a : Type) = {
  Ok : 'a,
  Nope : unit,
}

register r : bits(1)

val f : forall 'n, 'n > 0. int('n) -> Foo(bits(8 * 'n))
function f(sz) = Ok(sail_zero_extend(r, 8 * sz))

val g : Params -> bits(64)

function g(p) = {
  let x = f(p.size);
  match x {
  Ok(v) => sail_zero_extend(v, 64),
  Nope(_) => sail_zeros(64),
  }
}
