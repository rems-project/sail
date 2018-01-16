val vector_access_dec : forall ('l : Int) ('a : Type), 'l >= 0.
  (vector('l, dec, 'a), range(0, 'l - 1)) -> 'a

val vector_access_inc : forall ('l : Int) ('a : Type), 'l >= 0.
  (vector('l, inc, 'a), range(0, 'l - 1)) -> 'a

overload vector_access = {vector_access_inc, vector_access_dec}

default Order dec

val test : vector(4, dec, bit) -> unit

function test v = {
  z = vector_access(v, 3);
  z = v[3]
}
