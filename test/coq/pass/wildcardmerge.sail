default Order dec
$include <prelude.sail>

/* Checks that when merging the type variable with the integer argument,
   that we name the integer so that we can write the type of the
   second argument. */

val f : forall 'n, 'n >= 0. (int('n), bits('n)) -> unit

function f(_,_) = ()
