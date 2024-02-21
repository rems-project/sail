default Order dec

$include <prelude.sail>

register R : bool = true

val main : unit -> unit

function main() = {
    if R then {
        print_endline("taken")
    } else {
        print_endline("not taken")
    }
}
