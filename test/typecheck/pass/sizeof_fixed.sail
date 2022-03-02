default Order dec

$include <prelude.sail>

val f : forall 'n. bits('n) -> int effect {escape}

function f(v) = {
    assert('n == 32);
    sizeof('n)
}
