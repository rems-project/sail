$ifndef _ARITH
$define _ARITH

$include <flow.sail>

// ***** Addition *****

val add_atom = {ocaml: "add_int", lem: "integerAdd", c: "add_int"} : forall 'n 'm.
  (atom('n), atom('m)) -> atom('n + 'm)

val add_int = {ocaml: "add_int", lem: "integerAdd", c: "add_int"} : (int, int) -> int

overload operator + = {add_atom, add_int}

// ***** Subtraction *****

val sub_atom = {ocaml: "sub_int", lem: "integerMinus", c: "sub_int"} : forall 'n 'm.
  (atom('n), atom('m)) -> atom('n - 'm)

val sub_int = {ocaml: "sub_int", lem: "integerMinus", c: "sub_int"} : (int, int) -> int

overload operator - = {sub_atom, sub_int}

// ***** Negation *****

val negate_atom = {ocaml: "negate", lem: "integerNegate", c: "neg_int"} : forall 'n. atom('n) -> atom(- 'n)

val negate_int = {ocaml: "negate", lem: "integerNegate", c: "neg_int"} : int -> int

overload negate = {negate_atom, negate_int}

// ***** Multiplication *****

val mult_atom = {ocaml: "mult", lem: "integerMult", c: "mult_int"} : forall 'n 'm.
  (atom('n), atom('m)) -> atom('n * 'm)

val mult_int = {ocaml: "mult", lem: "integerMult", c: "mult_int"} : (int, int) -> int

overload operator * = {mult_atom, mult_int}

val "print_int" : (string, int) -> unit

// ***** Integer shifts *****

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

// ***** div and mod *****

val div_int = {
  smt: "div",
  ocaml: "quotient",
  lem: "integerDiv",
  c: "div_int"
} : (int, int) -> int

overload operator / = {div_int}

val mod_int = {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod",
  c: "mod_int"
} : (int, int) -> int

overload operator % = {mod_int}

val abs_int = {
  smt : "abs",
  ocaml: "abs_int",
  lem: "abs_int"
} : (int, int) -> int

$endif
