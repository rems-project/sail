default Order dec

infix 4 ==

val operator == = pure {lem: "eq_vec"} : forall 'n. (bitvector('n, dec), bitvector('n, dec)) -> bool

struct ProcState('n) = {
  N : bitvector('n, dec),
  Z : bitvector(1, dec),
  C : bitvector(1, dec),
  V : bitvector(1, dec)
}

register PSTATE : ProcState(1) = struct { N = 0b0, Z = 0b0, C = 0b0, V = 0b0 }

function test () -> bool = PSTATE.N == 0b1
