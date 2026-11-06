default Order dec

$include <prelude.sail>

register R : bits(16)

val main : unit -> unit

function main() = {
    let x = ref R;
    *x = 0xFFFF;
    print_bits("*x = ", *x)
}
