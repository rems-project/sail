default Order dec
$include <prelude.sail>

val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec b =
  match b {
    bitzero => 0b0,
    bitone  => 0b1
  }
