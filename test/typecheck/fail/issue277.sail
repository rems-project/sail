default Order dec

$include <prelude.sail>

type xlen : Int = 64

val foo : int(32) -> unit

val main : unit -> unit

function main() = {
    foo(sizeof(xlen))
}
