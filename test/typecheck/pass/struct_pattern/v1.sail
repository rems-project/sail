default Order dec

$include <prelude.sail>

struct foo = {
    field1 : bits(32),
    field2 : int
}

val main : unit -> unit

function main() = {
    match struct { field1 = 0xFFFF_ABCD, field2 = 3 } : foo {
        struct { field1 = b, _, _ } => {
            print_bits("field1 = ", b);
            print_int("field2 = ", i);
        }
    }
}
