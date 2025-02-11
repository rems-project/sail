import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def foo (_ : Unit) : Bool :=
  true

def initialize_registers (_ : Unit) : Unit :=
  ()

