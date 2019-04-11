default Order dec

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>

enum E = A | B | C

struct S = {
  field1 : bits(8),
  field2 : bits(16),
  field3 : E
}

register R1 : bits(16)
register R2 : bits(8)

$property
function prop(x: bool) -> bool = {
  if x then {
    R1 = 0x00FF
  } else {
    R1 = 0xFFFF
  };
  R1 == sail_zero_extend(R2, 16)
}
