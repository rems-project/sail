default Order dec
$include <prelude.sail>

mapping m : int <-> bool = {
  forwards x if x > 0 => true when x < 5,
  backwards _ => 0
}
