default Order dec

$include <prelude.sail>

/* Should this actually be forbidden? Currently allowed because we can
always construct Baz() even when Bar is uninhabited. */

union Foo('n: Int) = {
    Bar : bits('n - 2),
    Baz : unit,
}

val foo : unit -> unit

function foo() = {
    let x: Foo(1) = undefined;
    ()
}
