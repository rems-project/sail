default Order dec
$include <prelude.sail>

/* Use functions to hide the fact that these are really small constants, so they are forced to be represented as big ints */

val big_five : unit -> int

function big_five() = 5

val big_zero : unit -> int

function big_zero() = 0

val main : unit -> unit

function main() = {
    print_bits("3 3 0 = ", get_slice_int(3, 3, 0));
    print_bits("3 5 0 = ", get_slice_int(3, 5, 0));
    print_bits("3 5 0 = ", get_slice_int(3, big_five(), 0));
    print_bits("5 5 0 = ", get_slice_int(big_five(), big_five(), 0));
    print_bits("5 5 1 = ", get_slice_int(big_five(), 5, 1));
    print_bits("5 5 0 = ", get_slice_int(big_five(), big_five(), big_zero()));
}