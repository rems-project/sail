val vector_access_dec : forall 'l ('a : Type), 'l >= 0.
  (vector('l, dec, 'a), range(0, 'l - 1)) -> 'a

val vector_access_inc : forall ('l : Int) ('a : Type), 'l >= 0.
  (vector('l, inc, 'a), range(0, 'l - 1)) -> 'a

default Order inc

overload vector_access = {vector_access_inc, vector_access_dec}

val test : vector(4, inc, bit) -> unit

function test v = {
  z = vector_access(v, 3);
  z = v[3]
}
