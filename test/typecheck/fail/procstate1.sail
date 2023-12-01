default Order dec

infix 4 ==

val operator == = pure {lem: "eq_vec"} : forall 'n. (bitvector('n, dec), bitvector('n, dec)) -> bool

struct ProcState ('n : Int) = {
  N : bitvector('n, dec),
  Z : bitvector(1, dec),
  C : bitvector(1, dec),
  V : bitvector(1, dec)
}

register PSTATE : ProcState(1)

function test () -> bool = PSTATE.N == 0b1
