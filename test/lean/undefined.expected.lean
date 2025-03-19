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


namespace Functions

/-- Type quantifiers: n : Int -/
def foo (n : Int) : SailM (Bool × (BitVec 1) × Int × Nat × (BitVec 3)) := do
  let t__0 ← do (undefined_bool ())
  let t__1 ← do (undefined_bit ())
  let t__2 ← do (undefined_int ())
  let t__3 ← do (undefined_nat ())
  let t__4 ← do (undefined_bitvector 3)
  (pure (t__0, t__1, t__2, t__3, t__4))

/-- Type quantifiers: n : Int -/
def bar (n : Int) : SailM (Vector Int 4) := do
  (undefined_vector 4 n)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
open Functions

