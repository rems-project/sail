default Order dec

type bit = bitvector(1)

val cast ex_int : int -> {'n, true. atom('n)}

val zeros : forall 'n. atom('n) -> vector('n, dec, bit)

val test : nat -> unit

function test n = { x = zeros(n); () }
