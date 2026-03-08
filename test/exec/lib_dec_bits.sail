default Order dec

$include <prelude.sail>
$include <dec_bits.sail>

function main() -> unit = {
    match dec_bits_1("1") {
        0b1 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match dec_bits_1(0b1) {
        "1" => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match dec_bits_8("255") {
        0b1111_1111 => print_endline("ok"),
        _ => print_endline("fail"),
    };
    match dec_bits_8(0b1111_1111) {
        "255" => print_endline("ok"),
        s => print_endline(s),
    };
    match dec_bits_8(0b1101_0000) {
        "208" => print_endline("ok"),
        s => print_endline("fail"),
    };
    match dec_bits_8("208") {
        0b1101_0000 => print_endline("ok"),
        s => print_endline("fail"),
    };
}
