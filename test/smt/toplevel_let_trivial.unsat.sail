default Order dec

$include <prelude.sail>

let T: bool = true

let T2 : bool = false

$property
function prop() -> bool = {
  T
}