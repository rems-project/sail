default Order dec

$include <prelude.sail>

$property
function prop forall 'n 'm, 'n == 'm. (x: int('n), y: int('m)) -> bool = x == y
