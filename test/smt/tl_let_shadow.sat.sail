default Order dec

$include <prelude.sail>

let xs = 0xFFFF_FFFF

$counterexample
function prop(xs: bits(32)) -> bool = {
  xs == 0xFFFF_FFFF
}