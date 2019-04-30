default Order dec

$include <prelude.sail>

$counterexample :query exist match_failure
function prop(xs: bits(4)) -> unit = {
  match xs {
    _ : bits(3) @ 0b0 => ()
  }
}
