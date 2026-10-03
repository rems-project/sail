default Order dec

$include <prelude.sail>

val ones : forall 'n, 'n >= 0. (implicit('n), unit) -> bits('n)
function ones(n, _) = {
  sail_ones(n)
}

register configuration R : bits(32) = ones()

register S : bits(32)

function main(() : unit) -> unit = {
    print_bits("R = ", R);
    R = sail_zeros(32);
    print_bits("R = ", R)
}
