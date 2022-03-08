$include <flow.sail>

val add_int = pure {ocaml: "add", lem: "integerAdd"}: (int, int) -> int

overload operator + = {add_int}

val sub_int = pure {ocaml: "sub", lem: "integerMinus"}: (int, int) -> int

overload operator - = {sub_int}

function foo w : int -> int = {
  x : int = w;
  y : int = w;
  foreach (z from 0 to 10 by 1 in inc) {
    x = x + z;
    y = y - z
  };
  x + y
}
