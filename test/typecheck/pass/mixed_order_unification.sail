default Order dec
$include <prelude.sail>

/* An example where inference of the type parameters needs
   unification on the arguments before unification on the result type can
   provide 'y, but there's no need to go back to the arguments afterwards. */

val f : forall 'x 'y 'z, 'x + 'y > 0. (int('x), int('z)) -> bits('x + 'y)

val g : unit -> bits(1)
function g() = f(0,2)
