default Order inc

val bv_add = {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (vector('n, inc, bit), vector('n, inc, bit)) -> vector('n, inc, bit)

val vector_subrange = {ocaml: "bitvector_subrange_inc", lem: "bitvector_subrange_inc"}: forall ('l : Int) ('m : Int) ('o : Int), 'l >= 0 & 'm <= 'o & 'o <= 'l.
  (vector('l, inc, bit), atom('m), atom('o)) -> vector('o + 1 - 'm, inc, bit)

val bitvector_concat : forall ('m : Int) ('p : Int).
  (vector('m, inc, bit), vector('p, inc, bit)) -> vector('m + 'p, inc, bit)

overload operator + = {bv_add}

overload append = {bitvector_concat}

val test : (vector(3, inc, bit), vector(3, inc, bit)) -> vector(3, inc, bit)

function test (x : vector(1, inc, bit) @ 0b1 @ 0b0, z) = (x @ 0b11) + z
