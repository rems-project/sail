default Order dec
$include <prelude.sail>

register R : vector(8, dec, bits(8))

val main : unit -> unit

function main() = {
    R[0] = 0xAB;
    let vec = [R with 0 = 0xCD];
    print_bits("R[0] = ", R[0]);
    print_bits("vec[0] = ", vec[0])
}