default Order dec

$include <prelude.sail>
$include <string.sail>

val main : unit -> unit

function main() = {
    assert(hex_str(14) == "0xe");
    assert(hex_str(15) == "0xf");
    assert(hex_str(16) == "0x10");
    assert(hex_str(243234802384) == "0x38a1ec8ad0");

    assert(hex_str_upper(14) == "0xE");
    assert(hex_str_upper(15) == "0xF");
    assert(hex_str_upper(16) == "0x10");
    assert(hex_str_upper(243234802384) == "0x38A1EC8AD0");
}
