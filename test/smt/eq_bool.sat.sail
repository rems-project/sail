default Order dec

$include <prelude.sail>
$include <generic_equality.sail>

$option --smt-disable-specialization

val eq_wrapper : forall 'a. 'a -> bool

function eq_wrapper(x) = not_bool(x == x)

$[counterexample]
val prop : bool -> bool

function prop(b) = {
  eq_wrapper(b : bool)
}
