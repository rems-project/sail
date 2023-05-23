default Order dec
$include <prelude.sail>

val f : (int, bits(4), int) -> int

function f (0,0x0,0) = 0
and f ((1,x,_) if match x {0x1 => false, _ => true}) = 1
and f (_,_,_) = 2
