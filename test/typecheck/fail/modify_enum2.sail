default Order dec
$include <prelude.sail>

enum E = A | B | C

val main : unit -> unit

function main() = {
    A: E = 0b1
}
