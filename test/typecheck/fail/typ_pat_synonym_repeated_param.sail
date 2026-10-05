default Order dec

$include <prelude.sail>

type dup('a : Type) = ('a, 'a)
function f(x : (int(1), int(2))) -> unit = match x { y as dup(int('n)) => () }
