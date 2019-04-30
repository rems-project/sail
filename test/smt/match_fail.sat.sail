default Order dec

$include <prelude.sail>

$counterexample
function prop(xs: bits(4)) -> bool = {
  match xs {
    _ : bits(3) @ 0b0 => true
  }
}
