default Order dec

$include <prelude.sail>
$include <option.sail>

$property
function prop() -> bool = {
  match Some(0) {
    None() => true,
    Some(a) => a == 0,
  }
}
