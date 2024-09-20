default Order dec

$include <prelude.sail>

struct Foo('n), 'n >= 2 = {
    xs: bits('n - 2)
}

type synonym('n: Int), 'n >= 2 = Foo('n)

val foo : unit -> unit

function foo() = {
    let x: synonym(1) = undefined;
    ()
}
