$ifndef _SMT
$define _SMT

// see http://smtlib.cs.uiowa.edu/theories-Ints.shtml

/*! Euclidean division */
val ediv_int = {
  ocaml: "quotient",
  interpreter: "quotient",
  lem: "integerDiv",
  c: "ediv_int",
  coq: "ediv_with_eq"
} : forall 'n 'm. (int('n), int('m)) -> int(div('n, 'm))

val emod_int = {
  ocaml: "modulus",
  interpreter: "modulus",
  lem: "integerMod",
  c: "emod_int",
  coq: "emod_with_eq"
} : forall 'n 'm. (int('n), int('m)) -> int(mod('n, 'm))

val abs_int_atom = {
  ocaml: "abs_int",
  interpreter: "abs_int",
  lem: "integerAbs",
  c: "abs_int",
  coq: "abs_with_eq"
} : forall 'n. int('n) -> int(abs('n))

overload abs_int = {abs_int_atom}

$ifdef TEST

let __smt_x : int(div(4, 2)) = div(8, 4)

$endif

$endif
