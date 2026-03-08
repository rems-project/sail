default Order dec

$include <prelude.sail>

register X : bits(4)

function get_X() -> register(bits(4)) = {
    ref X
}

function main() -> unit = {
    (*get_X()) = 0xA;

    print_bits("register value = ", X);
}
