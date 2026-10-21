default Order dec

$include <prelude.sail>

type bytes('n : Int), 'n >= 0 = bits(8 * 'n)
function f(x : bits(33)) -> unit = match x { y as bytes('n) => () }
