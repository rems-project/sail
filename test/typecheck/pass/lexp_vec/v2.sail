default Order dec

$include <prelude.sail>

register V : vector(16, dec, bitvector(32, dec))

val zeros : forall 'n, 'n >= 0. unit -> bitvector('n, dec)

val write_V : forall 'i, 0 <= 'i < 16. (int('i), bitvector(32, dec)) -> unit effect {wreg}

function write_V(i, v) = {
  V[i] = v
}

function main() : unit -> unit = {
  write_V(16, zeros())
}
