import Out.Sail.Sail
import Out.Sail.BitVec

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

def foo (y : Unit) : Unit :=
  y

def initialize_registers (_ : Unit) : Unit :=
  ()

