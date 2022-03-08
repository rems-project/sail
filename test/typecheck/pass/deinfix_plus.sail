default Order inc

val bv_add = pure {ocaml: "add_vec", lem: "add_vec", coq: "add_vec"}: forall ('n : Int).
  (bitvector('n, inc), bitvector('n, inc)) -> bitvector('n, inc)

overload operator + = {bv_add}

val test : (bitvector(3, inc), bitvector(3, inc)) -> bitvector(3, inc)

function test (x, y) = x + y
