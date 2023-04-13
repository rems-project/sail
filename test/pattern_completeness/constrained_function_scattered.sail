default Order dec

$include <prelude.sail>

val foo : forall 'n, 'n in {32, 64}. int('n) -> unit

function clause foo 64 = ()

function clause foo 32 = ()
