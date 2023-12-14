default Order dec

$include <prelude.sail>

val foo : forall 'n. int('n) -> unit

function foo forall 'n. (x: int('n)) -> unit = ()

