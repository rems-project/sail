default Order dec

$include <prelude.sail>

function f(x : bits(4)) -> unit = match x { y as bits(int('n)) => () }
