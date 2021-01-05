$ifndef _GENERIC_EQUALITY
$define _GENERIC_EQUALITY

$include <flow.sail>

val eq_anything = {ocaml: "(fun (x, y) -> x = y)", interpreter: "eq_anything", lem: "eq", coq: "generic_eq", c: "eq_anything"} : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_anything}

val neq_anything : forall ('a : Type). ('a, 'a) -> bool

function neq_anything(x, y) = not_bool(eq_anything(x, y))

overload operator != = {neq_anything}

$endif
