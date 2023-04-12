default Order dec

$include <prelude.sail>

val foo : forall 'n 'm, 'n in {32, 64}. (int('n), bits('m)) -> unit

function foo(x, y) = {
    if sizeof('m) == 64 then {
        match (x, y) {
            (32, 0b00 @ _ @ _ @ 0b11) => (),
            (64, _) => (),
        }
    }
}
