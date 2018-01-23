default Order inc

val bv_add = {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (vector('n, inc, bit), vector('n, inc, bit)) -> vector('n, inc, bit)

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_inc"}: forall ('l : Int) ('m : Int) ('o : Int), 'l >= 0 & 'm <= 'o & 'o <= 'l.
  (vector('l, inc, bit), atom('m), atom('o)) -> vector('o + 1 - 'm, inc, bit)

val bitvector_concat = {ocaml: "append", lem: "concat_vec"} : forall ('m : Int) ('p : Int).
  (vector('m, inc, bit), vector('p, inc, bit)) -> vector('m + 'p, inc, bit)

val eq_vec = {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (vector('n, inc, bit), vector('n, inc, bit)) -> bool

infix 4 ==
overload operator == = {eq_vec}

overload operator + = {bv_add}

overload append = {bitvector_concat}

val test : (vector(3, inc, bit), vector(3, inc, bit)) -> vector(3, inc, bit)

function test (x : vector(1, inc, bit) @ 0b1 @ 0b0, z) = (x @ 0b11) + z
