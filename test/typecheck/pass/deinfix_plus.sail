default Order inc

val bv_add = {ocaml: "add_vec", lem: "add_vec", coq: "add_vec"}: forall ('n : Int).
  (vector('n, inc, bit), vector('n, inc, bit)) -> vector('n, inc, bit)

overload operator + = {bv_add}

val test : (vector(3, inc, bit), vector(3, inc, bit)) -> vector(3, inc, bit)

function test (x, y) = x + y
