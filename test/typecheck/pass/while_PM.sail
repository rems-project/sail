default Order dec

val lt_range_atom = {ocaml: "lt", lem: "lt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val lt_int = {ocaml: "lt", lem: "lt"}: (int, int) -> bool

overload operator < = {lt_range_atom, lt_int}

val add_range = {ocaml: "add", lem: "add"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = {ocaml: "add", lem: "add"}: (int, int) -> int

overload operator + = {add_range, add_int}

val vector_access = "bitvector_access_dec" : forall ('l : Int), 'l >= 0.
  (vector('l, dec, bit), int) -> bit

register GPR00 : vector(64, dec, bit)

function test b : bit -> unit = {
  i : int = 0;
  while i < 64 do {
    GPR00[i] = b;
    i = i + 1
  }
}
