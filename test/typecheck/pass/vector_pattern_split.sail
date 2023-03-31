default Order dec

$include <prelude.sail>

val bar : unit -> {'n, 16 <= 'n <= 48. int('n)}

val foo : bits(64) -> unit

function foo(xs) = {
    let 'n = bar();
    assert('n == 32);
    match xs {
        _ : bits('n) @ _ : bits(64 - 'n) => (),
    }
}
