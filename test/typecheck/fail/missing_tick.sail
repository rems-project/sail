default Order dec
$include <vector_dec.sail>

let 'x = 0
type foo = bits(x)

function y() : unit -> foo = sail_zeros(0)
