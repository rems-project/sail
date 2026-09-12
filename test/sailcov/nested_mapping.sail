default Order dec
$include <prelude.sail>

union ast = {
  B : (bool),
  Z : unit
}

mapping bool_not_bits : bool <-> bits(1) = {
  true   <-> 0b0,
  false  <-> 0b1
}

mapping encdec  : bits(2) <->  ast = {
  0b1 @ bool_not_bits(s) if true <-> B(s),
  0b00 <-> Z()
}

val main : unit -> unit
function main() = {
    let _ = encdec(0b00)
}
