import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: k_a : Type -/
def foo (x : k_a) : (k_a × k_a) :=
  (x, x)

def initialize_registers (_ : Unit) : Unit :=
  ()

