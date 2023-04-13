default Order dec

$include <prelude.sail>

val lookup : (bits(8), list(bits(8))) -> bits(8)

function lookup(x, table) = {
    match (x, table) {
        (0x00, x :: _) => x,
        (_, _ :: xs)   => lookup(sub_bits(x, 0x01), xs)
    }
}
