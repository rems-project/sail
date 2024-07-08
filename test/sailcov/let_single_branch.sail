default Order dec
$include <prelude.sail>

register R : bool = true
val main : unit -> unit

function main() = {
    let (x, y) = (R, R);
    if x then {
        print_endline("A")
    } else {
        print_endline("B")
    }
}
