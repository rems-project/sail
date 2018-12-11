$ifndef _FLOW
$define _FLOW

/*

This file contains the basic definitions for equality and comparison
that is required for flow typing to work correctly. It should
therefore be included in just about every Sail specification.

*/

val eq_unit : (unit, unit) -> bool

val eq_bit = { lem : "eq", _ : "eq_bit" } : (bit, bit) -> bool

function eq_unit(_, _) = true

val not_bool = {coq: "negb", _: "not"} : bool -> bool
/* NB: There are special cases in Sail for effectful uses of and_bool and
   or_bool that are not shown here. */
val and_bool = {coq: "andb", _: "and_bool"} : (bool, bool) -> bool
val or_bool = {coq: "orb", _: "or_bool"} : (bool, bool) -> bool
val eq_int = {ocaml: "eq_int", lem: "eq", c: "eq_int", coq: "Z.eqb"} : (int, int) -> bool
val eq_bool = {ocaml: "eq_bool", lem: "eq", c: "eq_bool", coq: "Bool.eqb"} : (bool, bool) -> bool

val neq_int = {lem: "neq"} : (int, int) -> bool
function neq_int (x, y) = not_bool(eq_int(x, y))

val neq_bool : (bool, bool) -> bool
function neq_bool (x, y) = not_bool(eq_bool(x, y))

val lteq_int = {coq: "Z.leb", _:"lteq"} : (int, int) -> bool
val gteq_int = {coq: "Z.geb", _:"gteq"} : (int, int) -> bool
val lt_int = {coq: "Z.ltb", _:"lt"} : (int, int) -> bool
val gt_int = {coq: "Z.gtb", _:"gt"} : (int, int) -> bool

overload operator == = {eq_int, eq_bit, eq_bool, eq_unit}
overload operator != = {neq_int, neq_bool}
overload operator | = {or_bool}
overload operator & = {and_bool}

overload operator <= = {lteq_int}
overload operator < = {lt_int}
overload operator >= = {gteq_int}
overload operator > = {gt_int}

$endif
