import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def foo (y : Unit) : Unit :=
  y

def initialize_registers (_ : Unit) : Unit :=
  ()

