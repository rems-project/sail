default Order dec

$include <prelude.sail>

register V : vector(1, dec, bitvector(32, dec))

val zeros : forall 'n, 'n >= 0. unit -> bitvector('n, dec)

function main() : unit -> unit = {
  V[0] = zeros()
}
