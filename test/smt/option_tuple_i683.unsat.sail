default Order dec

$include <prelude.sail>
$include <option.sail>

$include <option.sail>

$property
function prop() -> bool = {
  match Some(0, 0) {
    None() => true,
    Some(a, b) => a == b
  }
}
