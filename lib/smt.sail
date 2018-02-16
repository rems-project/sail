$ifndef _SMT
$define _SMT

// see http://smtlib.cs.uiowa.edu/theories-Ints.shtml

val div = {
  smt: "div",
  ocaml: "quotient",
  lem: "integerDiv"
} : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o = div('n, 'm). atom('o)}

val mod = {
  smt: "mod",
  ocaml: "modulus",
  lem: "integerMod"
} : forall 'n 'm. (atom('n), atom('m)) -> {'o, 'o = mod('n, 'm). atom('o)}

val abs_atom = {
  smt : "abs",
  ocaml: "abs_int",
  lem: "abs_int"
} : forall 'n. atom('n) -> {'o, 'o = abs_atom('n). atom('o)}

$ifdef TEST

let __smt_x : atom(div(4, 2)) = div(8, 4)

$endif

$endif
