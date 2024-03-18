default Order dec

$include <prelude.sail>

function test forall 'n, 'n > 0. (
    n : int('n)
) -> {'m, 'm == 'n + 1. int('m)} = {
    n + 1
}
