default Order inc

val add_vec = monadic {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (bitvector('n, inc), bitvector('n, inc)) -> bitvector('n, inc)

val add_range = monadic {ocaml: "add_range", lem: "add_range"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val cast unsigned : forall ('n : Int).
  bitvector('n, inc) -> range(0, 2 ^ 'n - 1)

overload operator + = {add_vec, add_range}

let x : range(0, 30) = 0xF + 0x2
