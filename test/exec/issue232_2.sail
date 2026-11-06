default Order dec
$include <prelude.sail>

enum E = EA | EB

mapping e_pair_bits : (E,E) <-> bits(2) =
  { (EA, EA) <-> 0b00
  , (EA, EB) <-> 0b01
  , (EB, EB) <-> 0b11
  }

struct eful =
  { e1 : E
  , e2 : E
  }

val eful_unpack : eful <-> (E,E)
function eful_unpack_backwards_matches(x) = true
function eful_unpack_forwards(s) = (s.e1, s.e2)
function eful_unpack_forwards_matches(x) = true
function eful_unpack_backwards(e1,e2) = struct { e1 = e1, e2 = e2 }

union F = { FE : eful }

val f_bits : F <-> bits(2)
mapping f_bits = { FE(eful_unpack(e1,e2)) <-> e_pair_bits(e1,e2) }

val main : unit -> unit

function main() = {
  print_bits("EA, EB = ", f_bits(FE(struct { e1 = EA, e2 = EB })))
}
