$ifndef _FLOW
$define _FLOW

/*

This file contains the basic definitions for equality and comparison
that is required for flow typing to work correctly. It should
therefore be included in just about every Sail specification.

*/

val eq_unit : (unit, unit) -> bool

val "eq_bit" : (bit, bit) -> bool

function eq_unit(_, _) = true

val not_bool = {coq: "negb", _: "not"} : bool -> bool
/* NB: There are special cases in Sail for effectful uses of and_bool and
   or_bool that are not shown here. */
val and_bool = {coq: "andb", _: "and_bool"} : (bool, bool) -> bool
val or_bool = {coq: "orb", _: "or_bool"} : (bool, bool) -> bool

val eq_atom = {ocaml: "eq_int", lem: "eq", c: "eq_int", coq: "Z.eqb"} : forall 'n 'm. (atom('n), atom('m)) -> bool

val neq_atom = {lem: "neq", coq: "neq_atom"} : forall 'n 'm. (atom('n), atom('m)) -> bool

function neq_atom (x, y) = not_bool(eq_atom(x, y))

val lteq_atom = {coq: "Z.leb", _: "lteq"} : forall 'n 'm. (atom('n), atom('m)) -> bool
val gteq_atom = {coq: "Z.geb", _: "gteq"} : forall 'n 'm. (atom('n), atom('m)) -> bool
val lt_atom = {coq: "Z.ltb", _: "lt"}     : forall 'n 'm. (atom('n), atom('m)) -> bool
val gt_atom = {coq: "Z.gtb", _: "gt"}     : forall 'n 'm. (atom('n), atom('m)) -> bool

val lt_range_atom = {coq: "ltb_range_l", _: "lt"}     : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val lteq_range_atom = {coq: "leb_range_l", _: "lteq"} : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val gt_range_atom = {coq: "gtb_range_l", _: "gt"}     : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val gteq_range_atom = {coq: "geb_range_l", _: "gteq"} : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val lt_atom_range = {coq: "ltb_range_r", _: "lt"}     : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val lteq_atom_range = {coq: "leb_range_r", _: "lteq"} : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val gt_atom_range = {coq: "gtb_range_r", _: "gt"}     : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val gteq_atom_range = {coq: "geb_range_r", _: "gteq"} : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool

val eq_range = {ocaml: "eq_int", lem: "eq", c: "eq_int", coq: "eq_range"} : forall 'n 'm 'o 'p. (range('n, 'm), range('o, 'p)) -> bool
val eq_int = {ocaml: "eq_int", lem: "eq", c: "eq_int", coq: "Z.eqb"} : (int, int) -> bool
val eq_bool = {ocaml: "eq_bool", lem: "eq", c: "eq_bool", coq: "Bool.eqb"} : (bool, bool) -> bool

val neq_range = {lem: "neq"} : forall 'n 'm 'o 'p. (range('n, 'm), range('o, 'p)) -> bool
function neq_range (x, y) = not_bool(eq_range(x, y))

val neq_int = {lem: "neq"} : (int, int) -> bool
function neq_int (x, y) = not_bool(eq_int(x, y))

val neq_bool : (bool, bool) -> bool
function neq_bool (x, y) = not_bool(eq_bool(x, y))

val lteq_int = {coq: "Z.leb", _:"lteq"} : (int, int) -> bool
val gteq_int = {coq: "Z.geb", _:"gteq"} : (int, int) -> bool
val lt_int = {coq: "Z.ltb", _:"lt"} : (int, int) -> bool
val gt_int = {coq: "Z.gtb", _:"gt"} : (int, int) -> bool

overload operator == = {eq_atom, eq_range, eq_int, eq_bit, eq_bool, eq_unit}
overload operator != = {neq_atom, neq_range, neq_int, neq_bool}
overload operator | = {or_bool}
overload operator & = {and_bool}

overload operator <= = {lteq_atom, lteq_range_atom, lteq_atom_range, lteq_int}
overload operator < = {lt_atom, lt_range_atom, lt_atom_range, lt_int}
overload operator >= = {gteq_atom, gteq_range_atom, gteq_atom_range, gteq_int}
overload operator > = {gt_atom, gt_range_atom, gt_atom_range, gt_int}

$ifdef TEST

val __flow_test : forall 'n 'm. (atom('n), atom('m)) -> unit

function __flow_test (x, y) = {
  if lteq_atom(x, y) then {
    _prove(constraint('n <= 'm))
  } else {
    _prove(constraint('n > 'm))
  }
}

$endif

$endif
