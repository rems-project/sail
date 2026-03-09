default Order dec
$include <prelude.sail>

/* Putting the integer for 'n inside a pair prevents the Coq backend from
   merging the type variable and the argument, so it has to be careful about
   the value passed to sail_zeros. */

val f : forall 'n, 'n > 0. (bool, (int('n), bool)) -> bits('n)

function f(b, p) = match p { (n, b2) => sail_zeros(n) }
