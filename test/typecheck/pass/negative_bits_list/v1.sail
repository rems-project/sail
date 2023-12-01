default Order dec

$include <prelude.sail>

val foo : unit -> unit

function foo() = {
    let x: list(bits(-1)) = [||];
    let z: list(bits(-1)) = [|undefined|];
    ()
}
