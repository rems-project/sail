import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

/-- Type quantifiers: k_a : Type -/
def foo (x : k_a) : (k_a × k_a) :=
  (x, x)

def initialize_registers (_ : Unit) : Unit :=
  ()

