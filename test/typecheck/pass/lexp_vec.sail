default Order dec

$include <prelude.sail>

register V : vector(1, dec, vector(32, dec, bit))

val zeros : forall 'n, 'n >= 0. unit -> vector('n, dec, bit)

function main() : unit -> unit = {
  V[0] = zeros()
}
