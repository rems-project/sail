default Order dec

$include <prelude.sail>

val foo : forall 'n, 'n in {32, 64}. int('n) -> unit

function foo 64 = ()
and foo 32 = ()
