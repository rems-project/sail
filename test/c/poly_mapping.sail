default Order dec

$include <prelude.sail>

val "parse_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bits('n)
val "valid_hex_bits" : forall 'n, 'n > 0. (int('n), string) -> bool

val hex_bits : forall 'n, 'n > 0. bits('n) <-> (int('n), string)

function hex_bits_forwards(bv) = (length(bv), hex_str_upper(unsigned(bv)))
function hex_bits_forwards_matches(bv) = true

function hex_bits_backwards(n, str) = parse_hex_bits(n, str)
function hex_bits_backwards_matches(n, str) = valid_hex_bits(n, str)

val main : unit -> unit

function main() = {
    match 0xFF {
        hex_bits(n, str) => print_int(str, n),
    };
    match (8, "0xFF") {
        hex_bits(bv) => print_bits("", bv),
    };
    match 0b111 {
        hex_bits(n, str) => print_int(str, n),
    };
    match (3, "0x7") {
        hex_bits(bv) => print_bits("", bv),
    }
}
