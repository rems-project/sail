default Order dec

$option -strict_var
$include <prelude.sail>

val main : unit -> unit

function main() = {
    var x = "Hello";
    var y = "World";
    (x, y) = (y, x);
    print_endline(y);
    print_endline(x)
}
