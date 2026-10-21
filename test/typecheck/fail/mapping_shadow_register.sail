default Order dec
$include <prelude.sail>

register R : int
mapping m : int <-> (int, unit) = { R <-> (R, ()) }
