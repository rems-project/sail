default Order dec

$include <prelude.sail>

struct Foo = {
    xs: bits(-3)
}

val foo : unit -> unit

function foo() = {
    let x: Foo = undefined;
    ()
}
