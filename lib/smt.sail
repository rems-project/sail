$ifndef _SMT
$define _SMT

// see http://smtlib.cs.uiowa.edu/theories-Ints.shtml

val div = {
  smt: "div",
  ocaml: "quotient",
  lem: "integerDiv",
  c: "tdiv_int",
  coq: "ediv_with_eq"
} : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o == div('n, 'm). atom('o)}

overload operator / = {div}

val mod = {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod",
  c: "tmod_int",
  coq: "emod_with_eq"
} : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o == mod('n, 'm). atom('o)}

overload operator % = {mod}

val abs_atom = {
  smt : "abs",
  ocaml: "abs_int",
  lem: "abs_int",
  c: "abs_int",
  coq: "abs_with_eq"
} : forall 'n. atom('n) -> {'o, 'o == abs_atom('n). atom('o)}

$ifdef TEST

let __smt_x : atom(div(4, 2)) = div(8, 4)

$endif

$endif
