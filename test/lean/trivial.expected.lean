import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

def foo (y : Unit) : Unit :=
  y

def initialize_registers (_ : Unit) : Unit :=
  ()

