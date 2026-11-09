default Order dec
$include <prelude.sail>

// The value matched on will have type bitvector(((('_#i + 1) - '_#i) + 1)), and Lean doesn't try
// to coerce it to the type of the patterns automatically, so check that we add a suitable hint.

function f(x : bits(16), i : range(0, 8)) -> int =
  match x[(i+1)..i] {
  0b00 => 5,
  0b01 => 12,
  0b10 => 43,
  0b11 => 123,
  }
