default Order dec
$include <prelude.sail>
$include <smt.sail>

/* The appearance of v in the application of f will need a cast because 'n gets
 * instantiated to div('p, 8).  This particular case is made harder because
 * when the type checker looks at the argument it still doesn't have a full
 * type because it doesn't know 'm, so it infers the type.  The cast insertion
 * normally uses differences between expected and inferred types to decide
 * where to put casts, but here we need to use the difference between the
 * instantiated type from the function and the inferred type. */

val f : forall 'm 'n, 'm > 0 & 'n > 0. (int('n), vector('m, bits('n * 8))) -> vector('m, bits('n * 8))

function f(_, v) = v

val g : forall 'p, 'p > 0. bitvector('p) -> bitvector('p)
function g(v) = {
  assert(constraint('p == 32));
  let v' = f(ediv_int('p, 8), [v]);
  v'[0]
}
