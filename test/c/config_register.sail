default Order dec

$include <prelude.sail>

function zeros forall 'n. (() : unit) -> bits('n) = {
  sail_zeros('n)
}

register configuration R : bits(32) = zeros()

register S : bits(32)

function main(() : unit) -> unit = {
    R = zeros();
    print_bits("R = ", R)
}