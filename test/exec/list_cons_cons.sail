default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
    let x: list(int) = 1 :: 2 :: [||];
    match x {
        _ :: second :: _ => print_int("second = ", second),
        _ => (),
    }
}