default Order dec
$include <prelude.sail>
$include <exception_basic.sail>

// The pretty printer has a special case to format do blocks without including let unit bindings
// like the one below; however, the legacy do-elaborator doesn't propagate the unit type in this
// case, so we need a workaround.

// Derived from an Arm decoding function which throws exceptions to indicate that this case is
// actually a different instruction

function f(x : bits(4)) -> int = {
  let _ : unit =
    if x == 0xc
    then throw Exception()
    else throw Exception();
  5
}
