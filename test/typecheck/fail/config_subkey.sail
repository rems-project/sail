default Order dec

$include <prelude.sail>

val main : unit -> unit

function main() = {
    print_endline(config a.b.c : string);
    print_endline(config a.b : string);
}
