default Order dec

$include <prelude.sail>

union Foo('n: Int) = {
    Bar : bits('n - 2),
}

val foo : unit -> unit

function foo() = {
    let x: Foo(1) = undefined;
    ()
}
