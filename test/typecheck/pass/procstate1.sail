default Order dec

infix 4 ==

val operator == = {lem: "eq_vec"} : forall 'n. (vector('n, dec, bit), vector('n, dec, bit)) -> bool

struct ProcState ('n : Int) = {
  N : vector('n, dec, bit),
  Z : vector(1, dec, bit),
  C : vector(1, dec, bit),
  V : vector(1, dec, bit)
}

register PSTATE : ProcState(1)

function test () -> bool = PSTATE.N == 0b1
