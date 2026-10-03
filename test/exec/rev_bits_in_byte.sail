default Order dec
$include <prelude.sail>

function rev_bits_in_byte (xs : bits(8)) -> bits(8) = {
    var ys = 0x00;
    foreach (i from 0 to 7) {
      ys[i] = xs[7-i]
    };
    ys
}

val main : unit -> unit

function main() = {
    print_bits("", rev_bits_in_byte(0x0F))
}
