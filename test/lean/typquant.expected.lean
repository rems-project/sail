import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: n : Int -/
def foo (n : Int) : (BitVec 4) :=
  (0xF : (BitVec 4))

/-- Type quantifiers: k_n : Int -/
def bar (x : (BitVec k_n)) : (BitVec k_n) :=
  x

def initialize_registers (lit : Unit) : Unit :=
  ()

