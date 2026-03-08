default Order dec

$include <prelude.sail>
$include <string.sail>

val main : unit -> unit

function main() = {
    print_endline(hex_str(10));
    print_endline(hex_str_upper(10));
    print_endline(hex_str(-10));
    print_endline(hex_str_upper(-10));
    print_endline(hex_str(0));
    print_endline(hex_str(0));
}
