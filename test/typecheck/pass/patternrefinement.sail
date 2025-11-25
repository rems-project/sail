default Order dec

$include <prelude.sail>

val test : forall 'n, 'n in {32, 64}. bitvector('n) -> bitvector(64)

function test v = match length(v) {
  32 => sail_zero_extend(v, 64),
  64 => v
}
