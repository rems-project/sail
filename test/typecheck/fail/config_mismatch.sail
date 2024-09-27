default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
    print_endline(config a.b);
    print_int("", config a.b : int);
}
