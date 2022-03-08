val vector_append = pure {ocaml: "append", lem: "concat_vec"}: forall 'l1 'l2 ('o : Order), 'l1 >= 0 & 'l2 >= 0.
  (vector('l1, 'o, bit), vector('l2, 'o, bit)) -> vector('l1 + 'l2, 'o, bit)

default Order inc

val test : forall 'n 'm, 'n >= 0 & 'm >= 0.
  (vector('n, inc, bit), vector('m, inc, bit)) -> vector('n + 'm, inc, bit)

function test (v1, v2) = vector_append(v1, v2)
