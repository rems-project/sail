default Order dec

$include <string.sail>
$include <mapping.sail>

val main : unit -> unit

function main() = {
    print_endline(string_take("Hello, World!", 5))
}
