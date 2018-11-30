$ifndef _OPTION
$define _OPTION

// The option type is treated specially by the lem backend, so it maps
// onto the lem maybe type. If the constructors are named differently,
// this won't work - also no other type should be created with
// constructors named Some or None.

union option('a: Type) = {
  Some : 'a,
  None : unit
}

val is_none : forall ('a : Type). option('a) -> bool

function is_none opt = match opt {
  Some(_) => false,
  None()  => true
}

val is_some : forall ('a : Type). option('a) -> bool

function is_some opt = match opt {
  Some(_) => true,
  None()  => false
}

$endif
