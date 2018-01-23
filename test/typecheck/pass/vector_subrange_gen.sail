val vector_access : forall ('l : Int) ('o : Order) ('a : Type), 'l >= 0.
  (vector('l, 'o, 'a), range(0, 'l - 1)) -> 'a

val vector_append : forall ('l1 : Int) ('l2 : Int) ('o : Order) ('a : Type), 'l1 >= 0 & 'l2 >= 0.
  (vector('l1, 'o, 'a), vector('l2, 'o, 'a)) -> vector('l1 + 'l2, 'o, 'a)

val vector_subrange = {ocaml: "subrange", lem: "subrange_vec_inc"} : forall ('l : Int) ('m : Int) ('o : Int), 'l >= 0 & 'm <= 'o & 'o <= 'l.
  (vector('l, inc, bit), atom('m), atom('o)) -> vector('o - 'm + 1, inc, bit)

val sub : forall ('n : Int) ('m : Int). (atom('n), atom('m)) -> atom('n - 'm)

val "length" : forall ('n : Int). vector('n, inc, bit) -> atom('n)

default Order inc

val test : forall 'n 'm, 'n >= 5.
  vector('n, inc, bit) -> vector('n - 1, inc, bit)

function test v = {
  z = vector_subrange(v, 0, sub('n, 2));
  z = v[0 .. sub('n, 2)];
  z
}
