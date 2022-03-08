default Order dec

infix 4 ==

val extz = pure {ocaml: "extz", lem: "extz_vec"}: forall ('n : Int) ('m : Int) ('ord : Order).
  (int('m), vector('n, 'ord, bit)) -> vector('m, 'ord, bit)

val length = pure {ocaml: "length", lem: "length"}: forall ('m : Int) ('ord : Order) ('a : Type).
  vector('m, 'ord, 'a) -> int('m)

val eq_vec = pure {ocaml: "eq_vec", lem: "eq_vec"}: forall ('m : Int) ('ord : Order).
  (vector('m, 'ord, bit), vector('m, 'ord, bit)) -> bool

val eq_int = pure {ocaml: "eq_atom", lem: "eq"}: forall ('n : Int) ('m : Int).
  (int('n), int('m)) -> bool('n == 'm)

val eq = pure {ocaml: "eq", lem: "eq"}: forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_vec, eq_int, eq}

val test : forall 'n, 'n in {32, 64}.
  vector('n, dec, bit) -> vector(64, dec, bit)

function test v = match length(v) {
  32 => extz(64, v),
  64 => v
}
