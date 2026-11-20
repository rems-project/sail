default Order dec

$include <prelude.sail>

// An effectful & or | is printed as Lean's <&&> or <||>, which have their own
// precedence and associativity.  An operand that is itself such an operator
// must keep the grouping of the Sail source: (a | b) & c must not become
// a | (b & c).

register R : int

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

val or_then_and : bool -> bool

function or_then_and(b) = (b | bump()) & boom()

val or_of_and : bool -> bool

function or_of_and(b) = b | (bump() & boom())

val and_then_or : bool -> bool

function and_then_or(b) = (b & bump()) | boom()

val and_of_or : bool -> bool

function and_of_or(b) = b & (bump() | boom())

val all_effectful : unit -> bool

function all_effectful() = (bump() | boom()) & (boom() | bump())

val takes_bool : bool -> bool

function takes_bool(b) = not_bool(b)

val as_argument : bool -> bool

function as_argument(b) = takes_bool((b | bump()) & boom())
