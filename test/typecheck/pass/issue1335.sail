default Order dec
$include <prelude.sail>

register v : vector(8, bits(8)) = vector_init(0x00)

function main() -> unit = {
    print_endline(bits_str(v[7]));
    print_endline(dec_str(length(v)));
    print_endline(if v[4][4] == bitone then "one" else "zero");
}
