default Order dec

$include <prelude.sail>

val test : forall 'n. int('n) -> int(if 'n == 0 then 32 else 64)

function test(n) = {
    if n == 0 then 32 else 64
}
