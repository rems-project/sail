default Order dec

$include <prelude.sail>

struct Foo('n: Int) = {
    xs: bits('n - 2)
}

type synonym('n: Int) = Foo('n)

val foo : unit -> unit

function foo() = {
    let x: synonym(1) = undefined;
    ()
}
