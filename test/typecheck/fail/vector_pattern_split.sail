default Order dec

$include <prelude.sail>

val bar : unit -> {'n, 16 <= 'n <= 48. int('n)}

function foo(xs: bits(64)) -> unit = {
    let 'n = bar();
    match xs {
        _ : bits('n) @ _ : bits(64 - 'n) => (),
    }
}