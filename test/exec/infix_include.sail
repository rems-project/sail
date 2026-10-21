default Order dec

$include <prelude.sail>
$include "includes/infix_op.sail"

val main : unit -> unit

function main() = {
    print_int("", 1 +++ 3)
}
