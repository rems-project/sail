default Order dec
$include <prelude.sail>
$include <generic_equality.sail>

// Regression test for https://github.com/rems-project/sail/issues/1555
//
// We allowed constant folding to create a lazy 'attempt to read a
// register' value, and constant folding would only fail at the point got
// evaluated/forced. The problem is the generic structural equality
// function didn't force the value so it just sees the lazy value and the
// actual enum value as being structurally different.

$option -Oconstant_fold

enum E = {A, B}

register R : E

function is_B() -> bool = R == B

function main() -> unit = {
  R = B;
  if is_B() then {
    print_endline("Is B")
  } else {
    print_endline("Is A")
  }
}
