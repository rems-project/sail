default Order dec
$include <prelude.sail>

function f(x : bitvector(4)) -> unit = match x { y as bitvector(int('n)) => () }
