default Order dec

$include <prelude.sail>

$option -c_prefix sailgen_

val main : unit -> unit

function main() = {
    let x: int = 3;
    print_int("x = ", 3)
}
