default Order dec

$include <prelude.sail>

type v8('a : Type) = vector(8, 'a)
function f(x : vector(4, int)) -> unit = match x { y as v8(_) => () }
