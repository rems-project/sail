import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

inductive Register : Type where
  | dummy
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .dummy => (BitVec 1)

instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg dummy
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Errors

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open Register

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg dummy (← (undefined_bit ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
