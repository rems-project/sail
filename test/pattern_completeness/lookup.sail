default Order dec

$include <prelude.sail>
$include <option.sail>

val lookup : (bits(8), list(bits(8))) -> option(bits(8))

function lookup(x, table) = {
    match (x, table) {
        (_, [||])      => None(),
        (0x00, x :: _) => Some(x),
        (_, _ :: xs)   => lookup(sub_bits(x, 0x01), xs)
    }
}
