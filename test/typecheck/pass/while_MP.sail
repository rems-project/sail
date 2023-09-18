default Order dec

val add_int = pure {ocaml: "add", lem: "integerAdd"}: (int, int) -> int

overload operator + = {add_int}

val bool_not = pure {ocaml: "not", lem: "not"}: bool -> bool

register INT : bool

function test () -> int = {
  count : int = 0;
  while bool_not(INT) do count = count + 1;
  return(count)
}
