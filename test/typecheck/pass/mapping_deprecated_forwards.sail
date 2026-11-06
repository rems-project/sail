default Order dec
$include <prelude.sail>

mapping m : int <-> bool = {
  1 => true,
  backwards _ => 0
}
