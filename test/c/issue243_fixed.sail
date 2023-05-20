default Order dec
$include <prelude.sail>

enum E = EA | EB

mapping e_pair_bits : (E,E) <-> bits(2) =
  { (EA, EA) <-> 0b00
  , (EA, EB) <-> 0b01
  , (EB, EB) <-> 0b11
  }

struct eful = { e1 : E, v1 : bits(1) }

union F = { FE : eful }

val f_bits : F <-> bits(3)
mapping f_bits = { FE(struct { e1 = e1, v1 = v1 }) <-> e_pair_bits(e1,EB) @ v1 }

val main : unit -> unit

function main() = {
  print_bits("", f_bits(FE(struct { e1 = EA, v1 = 0b0 })));
  print_bits("", f_bits(FE(struct { e1 = EA, v1 = 0b1 })));
  print_bits("", f_bits(FE(struct { e1 = EB, v1 = 0b1 })))
}