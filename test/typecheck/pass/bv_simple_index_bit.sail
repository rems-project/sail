val bitvector_access_dec : forall ('n : Int), 'n >= 0.
  (vector('n, dec, bit), range(0, 'n - 1)) -> bit

val bitvector_access_inc : forall ('n : Int), 'n >= 0.
  (vector('n, inc, bit), range(0, 'n - 1)) -> bit

overload vector_access = {bitvector_access_inc, bitvector_access_dec}

val bv : vector(64, inc, bit) -> bit

function bv x = x[32]
