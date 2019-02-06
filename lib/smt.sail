$ifndef _SMT
$define _SMT

// see http://smtlib.cs.uiowa.edu/theories-Ints.shtml

val div = {
  ocaml: "quotient",
  lem: "integerDiv",
  c: "tdiv_int",
  coq: "ediv_with_eq"
} : forall 'n 'm. (int('n), int('m)) -> int(div('n, 'm))

overload operator / = {div}

val mod = {
  ocaml: "modulus",
  lem: "integerMod",
  c: "tmod_int",
  coq: "emod_with_eq"
} : forall 'n 'm. (int('n), int('m)) -> int(mod('n, 'm))

overload operator % = {mod}

val abs_int = {
  ocaml: "abs_int",
  lem: "abs_int",
  c: "abs_int",
  coq: "abs_with_eq"
} : forall 'n. int('n) -> int(abs('n))

$ifdef TEST

let __smt_x : int(div(4, 2)) = div(8, 4)

$endif

$endif
