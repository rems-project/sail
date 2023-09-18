default Order dec

val add_int = {ocaml: "add", lem: "add"}: (int, int) -> int

val add_vec_int : forall ('n : Int) ('ord : Order).
  (bitvector('n, 'ord), int) -> bitvector('n, 'ord)

overload operator + = {add_vec_int, add_int}

val bool_not = pure {ocaml: "not", lem: "not"}: bool -> bool

register COUNT : bitvector(64, dec)

register INT : bool

function test () -> unit = {
  COUNT = 0x0000_0000_0000_0000;
  while bool_not(INT) do COUNT = COUNT + 1
}
