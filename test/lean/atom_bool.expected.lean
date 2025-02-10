import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def foo (lit : Unit) : Bool :=
  true

def initialize_registers (lit : Unit) : Unit :=
  ()

