default Order dec

$include <prelude.sail>

val f : unit -> unit

function f() = {
    let x = 2;
    match x {
        2 => (),
    }
}
