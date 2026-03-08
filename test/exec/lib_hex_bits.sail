default Order dec

$include <prelude.sail>
$include <hex_bits.sail>

function main() -> unit = {
    match hex_bits_1("0x1") {
        0b1 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match hex_bits_1(0b1) {
        "0x1" => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match hex_bits_32("0xFFFFFFFF") {
        0xFFFF_FFFF => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match hex_bits_32("0xffffffff") {
        0xFFFF_FFFF => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match hex_bits_32(0xFFFF_FFFF) {
        "0xffffffff" => print_endline("ok"),
        s => print_endline(s),
    };
    match hex_bits_32(0xFFFF_FFFF) {
        "0xFFFFFFFF" => print_endline("fail"),
        s => print_endline(concat_str("ok ", s)),
    }
}
