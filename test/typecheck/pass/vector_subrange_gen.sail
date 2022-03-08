
val vector_subrange = pure {ocaml: "subrange", lem: "subrange_vec_inc"} : forall ('l : Int) ('m : Int) ('o : Int), 'l >= 0 & 'm <= 'o & 'o <= 'l.
  (bitvector('l, inc), atom('m), atom('o)) -> bitvector('o - 'm + 1, inc)

val sub : forall ('n : Int) ('m : Int). (atom('n), atom('m)) -> atom('n - 'm)

val bitvector_length = pure "length" : forall ('n : Int). bitvector('n, inc) -> atom('n)

overload __size = {bitvector_length}

default Order inc

val test : forall 'n 'm, 'n >= 5.
  bitvector('n, inc) -> bitvector('n - 1, inc)

function test v = {
  z = vector_subrange(v, 0, sub('n, 2));
  z = v[0 .. sub('n, 2)];
  z
}
