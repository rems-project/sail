default Order inc

val bv_add = pure {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (bitvector('n, inc), bitvector('n, inc)) -> bitvector('n, inc)

val vector_subrange = pure {ocaml: "subrange", lem: "subrange_vec_inc"}: forall ('l : Int) ('m : Int) ('o : Int), 'l >= 0 & 'm <= 'o & 'o <= 'l.
  (bitvector('l, inc), atom('m), atom('o)) -> bitvector('o + 1 - 'm, inc)

val bitvector_concat = pure {ocaml: "append", lem: "concat_vec"} : forall ('m : Int) ('p : Int).
  (bitvector('m, inc), bitvector('p, inc)) -> bitvector('m + 'p, inc)

val eq_vec = pure {ocaml: "eq_list", lem: "eq_vec"} : forall 'n. (bitvector('n, inc), bitvector('n, inc)) -> bool

infix 4 ==
overload operator == = {eq_vec}

overload operator + = {bv_add}

overload append = {bitvector_concat}

val test : (bitvector(3, inc), bitvector(3, inc)) -> bitvector(3, inc)

function test (x : bitvector(1, inc) @ 0b1 @ 0b0, z) = (x @ 0b11) + z
