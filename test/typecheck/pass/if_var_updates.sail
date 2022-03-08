val add_int = pure {ocaml: "add", lem: "integerAdd"}: (int, int) -> int

overload operator + = {add_int}

val sub_int = pure {ocaml: "sub", lem: "integerMinus"}: (int, int) -> int

overload operator - = {sub_int}

val lt_int = pure {ocaml: "lt_int", lem: "lt"} : (int, int) -> bool

overload operator < = {lt_int}

function foo w : int -> (bool, int) = {
  x : int = w;
  y : int = 0 - w;
  let pos : bool =
    if (w < 0) then {
      x = 0 - x;
      false
    } else {
      y = 0 - w;
      true
    };
  (pos, x + y)
}
