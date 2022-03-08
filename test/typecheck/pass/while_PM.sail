default Order dec

val lt_range_atom = pure {ocaml: "lt", lem: "lt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val lt_int = pure {ocaml: "lt", lem: "lt"}: (int, int) -> bool

overload operator < = {lt_range_atom, lt_int}

val add_range = pure {ocaml: "add", lem: "integerAdd"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = pure {ocaml: "add", lem: "integerAdd"}: (int, int) -> int

overload operator + = {add_range, add_int}

val vector_access = pure {ocaml: "access", lem: "access_vec_dec"} : forall ('l : Int), 'l >= 0.
  (vector('l, dec, bit), int) -> bit

val vector_update = pure {ocaml: "update", lem: "update_vec_dec"} : forall 'n.
  (vector('n, dec, bit), int, bit) -> vector('n, dec, bit)

register GPR00 : vector(64, dec, bit)

/* FIXME: Currently this doesn't work in lem
function test b : bit -> unit = {
  i : range(0, 64) = 0;
  while i < 64 do {
    GPR00[i] = b;
    i = i + 1;
  }
}
*/