default Order dec

$include <prelude.sail>

val zeros : forall 'n, 'n >= 0. (implicit('n), unit) -> bits('n)
function zeros(n, _) = {
  sail_zeros(n)
}

register configuration R : bits(32) = zeros()

register S : bits(32)

function main(() : unit) -> unit = {
    R = zeros();
    print_bits("R = ", R)
}