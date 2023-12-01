default Order dec

$include <prelude.sail>

/* Should this actually be allowed? Currently forbidden because the undefined generation is strict */

union Foo('n: Int) = {
    Bar : bits('n - 2),
    Baz : unit,
}

val foo : unit -> unit

function foo() = {
    let x: Foo(1) = undefined;
    ()
}
