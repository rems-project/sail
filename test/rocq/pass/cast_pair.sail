default Order dec
$include <prelude.sail>

val f1 : bool -> (bits(3), bits(8))
function f1(b) = if b then (0b000, 0x12) else (0b111, 0x34)
val f2 : bool -> (bits(3), bits(16))
function f2(b) = if b then (0b000, 0x1234) else (0b111, 0x5678)

val g : forall 'n, 'n in {8,16}. bits('n) -> (bits(3), bits('n))

function g(v) = {
  match 'n {
  8 => f1(v == 0x00),
  16 => f2(v == 0x0000),
  }
}
