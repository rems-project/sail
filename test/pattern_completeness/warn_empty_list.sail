default Order dec

$include <prelude.sail>

function foo(x: list(int)) -> unit = {
    match x {
        [||] => (),
    }
}
