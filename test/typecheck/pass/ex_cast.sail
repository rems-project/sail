default Order dec

val cast ex_int : int -> {'n, true. atom('n)}

val zeros : forall 'n. atom('n) -> vector('n, dec, bit)

val test : int -> unit

function test n = { x = zeros(n); () }
