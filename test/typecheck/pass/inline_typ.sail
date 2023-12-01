default Order dec

$include <prelude.sail>

function test forall 'n 'm. (x : int('n), y : int('m)) -> int('m + 'n) = x + y
