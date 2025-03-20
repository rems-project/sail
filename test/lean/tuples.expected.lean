import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Sail.IntRange
import Out.Defs
import Out.Specialization

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

def let5 := (20, 300000000000000000000000)

def y :=
  let (y, z) := let5
  y

def z :=
  let (y, z) := let5
  z

def tuple1 (_ : Unit) : (Int × Int × ((BitVec 2) × Unit)) :=
  let t__4 := ((0b10 : (BitVec 2)), ())
  (3, 5, t__4)

def tuple2 (_ : Unit) : SailM (Int × Int) := do
  let t__0 ← do (undefined_int ())
  let t__1 ← do (undefined_int ())
  (pure (t__0, t__1))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
