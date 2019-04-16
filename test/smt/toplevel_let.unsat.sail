default Order dec

$include <prelude.sail>

let I: int = 3

let B: bits(64) = get_slice_int(64, I, 0)

$property
function prop() -> bool = {
  3 == I & I - unsigned(B) == 0
}