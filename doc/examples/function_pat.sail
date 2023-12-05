default Order dec

$include <prelude.sail>

$span start EXAMPLE
struct S = {
    field1 : int,
    field2 : string,
}

function example1(s : S) -> unit = {
    // Destructure 's' using let
    let struct { field1, _ } = s;
    print_int("field1 = ", field1)
}

// Destructure directly in the function argument
function example2(struct { field1, _ } : S) -> unit = {
    print_int("field1 = ", field1)
}
$span end
