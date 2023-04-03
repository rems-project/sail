default Order dec

$include <prelude.sail>

struct Foo = {
    xs: {'n, 'n == -1. bits('n)}
}

val foo : unit -> unit

function foo() = {
    let x: Foo = undefined;
    ()
}
