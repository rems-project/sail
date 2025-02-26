import Out.Sail.Sail
import Out.Sail.BitVec

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail


abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Defs

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail



namespace Functions

def foo (_ : Unit) : Bool :=
  true

def initialize_registers (_ : Unit) : Unit :=
  ()

end Functions
open Functions

