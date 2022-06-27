default Order dec
$include <prelude.sail>

val f : bits(64) -> int

function f(v) = {
  match v {
  _ : bits(62) @ 0b00 => 1,
  _ : bits(62) @ 0b01 => 2,
  _ : bits(62) @ 0b10 => 3,
  _ : bits(62) @ 0b11 => 4,
  }
}
