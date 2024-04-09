default Order dec

$include <prelude.sail>

$property
function prop forall 'n. (x: int('n), y: int('n)) -> bool = x == y
