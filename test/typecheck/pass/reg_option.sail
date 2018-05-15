$include <arith.sail>
$include <flow.sail>
$include <option.sail>

register X : option(int)

val inc_X : unit -> int effect {rreg, wreg}
function inc_X () = {
  let x : int = match X {
    Some(x) => x + 1,
    None() => 0
  };
  X = Some(x);
  return x;
}

