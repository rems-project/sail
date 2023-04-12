default Order dec

$include <prelude.sail>

val foo : unit -> unit

function foo() = {
    let x: (bits(-1), int) = undefined;
    ()
}
