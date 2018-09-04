$ifndef _ARITH
$define _ARITH

$include <flow.sail>

// ***** Addition *****

val add_atom = {ocaml: "add_int", lem: "integerAdd", c: "add_int", coq: "Z.add"} : forall 'n 'm.
  (int('n), int('m)) -> int('n + 'm)

val add_int = {ocaml: "add_int", lem: "integerAdd", c: "add_int", coq: "Z.add"} : (int, int) -> int

overload operator + = {add_atom, add_int}

// ***** Subtraction *****

val sub_atom = {ocaml: "sub_int", lem: "integerMinus", c: "sub_int", coq: "Z.sub"} : forall 'n 'm.
  (int('n), int('m)) -> int('n - 'm)

val sub_int = {ocaml: "sub_int", lem: "integerMinus", c: "sub_int", coq: "Z.sub"} : (int, int) -> int

overload operator - = {sub_atom, sub_int}

val sub_nat = {
  ocaml: "(fun (x,y) -> let n = sub_int (x,y) in if Big_int.less_equal n Big_int.zero then Big_int.zero else n)",
  lem: "integerMinus",
  _: "sub_nat"
} : (nat, nat) -> nat

// ***** Negation *****

val negate_atom = {ocaml: "negate", lem: "integerNegate", c: "neg_int", coq: "Z.opp"} : forall 'n. int('n) -> int(- 'n)

val negate_int = {ocaml: "negate", lem: "integerNegate", c: "neg_int", coq: "Z.opp"} : int -> int

overload negate = {negate_atom, negate_int}

// ***** Multiplication *****

val mult_atom = {ocaml: "mult", lem: "integerMult", c: "mult_int", coq: "Z.mul"} : forall 'n 'm.
  (int('n), int('m)) -> int('n * 'm)

val mult_int = {ocaml: "mult", lem: "integerMult", c: "mult_int", coq: "Z.mul"} : (int, int) -> int

overload operator * = {mult_atom, mult_int}

val "print_int" : (string, int) -> unit

val "prerr_int" : (string, int) -> unit

// ***** Integer shifts *****

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

// ***** div and mod *****

val div_int = {
  smt: "div",
  ocaml: "quotient",
  lem: "integerDiv",
  c: "tdiv_int",
  coq: "Z.quot"
} : (int, int) -> int

overload operator / = {div_int}

val mod_int = {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod",
  c: "tmod_int",
  coq: "Z.rem"
} : (int, int) -> int

overload operator % = {mod_int}

val abs_int = {
  smt : "abs",
  ocaml: "abs_int",
  lem: "abs_int",
  coq: "Z.abs"
} : (int, int) -> int

$endif
