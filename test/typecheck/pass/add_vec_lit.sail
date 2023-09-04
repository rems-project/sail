default Order inc
$include <arith.sail>

val add_vec = pure {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (bitvector('n, inc), bitvector('n, inc)) -> bitvector('n, inc)

val unsigned : forall ('n : Int).
  bitvector('n, inc) -> range(0, 2 ^ 'n - 1)

overload operator + = {add_vec}

let x : range(0, 30) = unsigned(0xF + 0x2)
let y : range(0, 30) = unsigned(0xF) + unsigned(0x2)

