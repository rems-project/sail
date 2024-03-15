default Order dec

$include <prelude.sail>

val test : forall 'n. int('n) -> {'m, ('n == 0 & 'm == 32) | ('n != 0 & 'm == 64). int('m)}

function test(n) = {
    if n == 0 then 32 else 64
}
