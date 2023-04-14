default Order dec

$include <prelude.sail>

val foo : forall 'n 'm, 'n in {32, 64} & 'm >= 2. (int('n), bits('m)) -> unit

function foo(x, y) = {
    match (x, y) {
        (32, 0b00 @ _ : bits('m - 2) @ 0b11) => (),
        (64, _) => (),
    }
}
