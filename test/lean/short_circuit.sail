default Order dec

$include <prelude.sail>

// Boolean & and | are short-circuiting: the right-hand operand must only be
// evaluated when the left-hand one does not determine the result.  When the
// right-hand operand is effectful it is printed as an if-then-else.  A pure
// right-hand operand stays an argument of && / ||: evaluating it cannot be
// observed, and a single boolean condition is easier for Lean proofs (such
// as termination) to use.

register R : int
register B : bool

val bump : unit -> bool

function bump() = {
  R = R + 1;
  true
}

val boom : unit -> bool

function boom() = {
  assert(false, "not short-circuited");
  true
}

val pure_and : (bool, bool) -> bool

function pure_and(a, b) = a & b

val pure_or : (bool, bool) -> bool

function pure_or(a, b) = a | b

val effectful_lhs : bool -> bool

function effectful_lhs(b) = B & b

val and_effect : bool -> bool

function and_effect(b) = b & boom()

val or_effect : bool -> bool

function or_effect(b) = b | bump()

val chain_and : (bool, bool) -> bool

function chain_and(a, b) = a & b & boom()

val chain_or : (bool, bool) -> bool

function chain_or(a, b) = a | bump() | boom()

val mixed : (bool, bool) -> bool

function mixed(a, b) = (a & boom()) | (b & bump())

val in_condition : bool -> int

function in_condition(b) = {
  if b & boom() then 1 else if b | bump() then 2 else 3
}

val in_let : bool -> bool

function in_let(b) = {
  let x = b & bump();
  let y = x | boom();
  x & y
}

val takes_bool : bool -> bool

function takes_bool(b) = not_bool(b)

val as_argument : bool -> bool

function as_argument(b) = takes_bool(b & bump())
