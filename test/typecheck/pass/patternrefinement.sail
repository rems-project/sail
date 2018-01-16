default Order dec

infix 4 ==

val extz = {ocaml: "extz", lem: "extz"}: forall ('n : Int) ('m : Int) ('ord : Order).
  vector('n, 'ord, bit) -> vector('m, 'ord, bit)

val length = {ocaml: "length", lem: "length"}: forall ('m : Int) ('ord : Order) ('a : Type).
  vector('m, 'ord, 'a) -> atom('m)

val eq_vec = {ocaml: "eq_vec", lem: "eq_vec"}: forall ('m : Int) ('ord : Order).
  (vector('m, 'ord, bit), vector('m, 'ord, bit)) -> bool

val eq_atom = {ocaml: "eq_atom", lem: "eq_atom"}: forall ('n : Int) ('m : Int).
  (atom('n), atom('m)) -> bool

val eq = {ocaml: "eq", lem: "eq"}: forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_vec, eq_atom, eq}

val test : forall 'n, 'n in {32, 64}.
  vector('n, dec, bit) -> vector(64, dec, bit)

function test v = match length(v) {
  32 => extz(v),
  64 => v
}
