default Order dec
$include <prelude.sail>

val f0 : forall 'n, 'n >= 0. int('n) -> (vector('n, dec, bool), vector('n, dec, bool))

/* Sail usually inserts a cast when translating the tuple assignment, but the
   type variable for `unsigned(v0)` was leaking into these casts.  It should
   manage to use 'n instead. */

val f : bits(4) -> unit

function f(v0) = {
  let num = unsigned(v0) * 8;
  let 'n = num;
  v1 : vector('n, dec, bool) = undefined;
  v2 : vector('n, dec, bool) = undefined;
  (v1, v2) = f0(num);
}
