default Order dec

infix 4 ==

val eq_atom = pure {ocaml: "eq_atom", lem: "eq", coq: "Z.eqb"}: forall ('n : Int) ('m : Int).
  (atom('n), atom('m)) -> bool

overload operator == = {eq_atom}

val test_fn : forall 'n, 'n in {8, 16}. atom('n) -> int

val test_switch : forall 'n, 'n in {8, 16}. atom('n) -> int

function test_fn 8 = 8
and test_fn 16 = 16

function test_switch n = match n {
  8 => 8,
  16 => 16
}
