default Order dec

val exts : forall ('n : Int) ('m : Int) ('ord : Order).
  vector('n, 'ord, bit) -> vector('m, 'ord, bit)

overload EXTS = {exts}

val add_vec : forall ('n : Int) ('ord : Order).
  (vector('n, 'ord, bit), vector('n, 'ord, bit)) -> vector('n, 'ord, bit)

overload operator + = {add_vec}

val test : (vector(32, dec, bit), vector(32, dec, bit)) -> unit

function test (x, y) = let z : vector(64, dec, bit) = add_vec(exts(x), exts(y)) in ()
