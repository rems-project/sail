$ifndef _FLOW
$define _FLOW

val not_bool = "not" : bool -> bool
val and_bool = "and_bool" : (bool, bool) -> bool
val or_bool = "or_bool" : (bool, bool) -> bool

val eq_atom = {ocaml: "eq_int", lem: "eq"} : forall 'n 'm. (atom('n), atom('m)) -> bool

val neq_atom = {lem: "neq"} : forall 'n 'm. (atom('n), atom('m)) -> bool

function neq_atom (x, y) = not_bool(eq_atom(x, y))

val lteq_atom = "lteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val gteq_atom = "gteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val lt_atom = "lt"     : forall 'n 'm. (atom('n), atom('m)) -> bool
val gt_atom = "gt"     : forall 'n 'm. (atom('n), atom('m)) -> bool

val lt_range_atom = "lt"     : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val lteq_range_atom = "lteq" : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val gt_range_atom = "gt"     : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val gteq_range_atom = "gteq" : forall 'n 'm 'o. (range('n, 'm), atom('o)) -> bool
val lt_atom_range = "lt"     : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val lteq_atom_range = "lteq" : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val gt_atom_range = "gt"     : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool
val gteq_atom_range = "gteq" : forall 'n 'm 'o. (atom('n), range('m, 'o)) -> bool

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
