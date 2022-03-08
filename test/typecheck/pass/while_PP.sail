default Order dec

val lt_range_atom = pure {ocaml: "lt", lem: "lt"}: forall ('n : Int) ('m : Int) ('o : Int).
  (range('n, 'm), atom('o)) -> bool

val lt_int = pure {ocaml: "lt", lem: "lt"}: (int, int) -> bool

overload operator < = {lt_range_atom, lt_int}

val mult_int : (int, int) -> int

overload operator * = {mult_int}

val add_range = pure {ocaml: "add", lem: "integerAdd"}: forall ('n : Int) ('m : Int) ('o : Int) ('p : Int).
  (range('n, 'm), range('o, 'p)) -> range('n + 'o, 'm + 'p)

val add_int = pure {ocaml: "add", lem: "integerAdd"}: (int, int) -> int

overload operator + = {add_range, add_int}

function test n : int -> int = {
  i : int = 1;
  j : int = 1;
  while i < n do {
    j = i * j;
    i = i + 1
  };
  j
}
