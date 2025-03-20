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
  | B
  | R
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .B => Bool
  | .R => Nat

instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg B
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg R
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Ite

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open Register

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R (← (undefined_nat ()))
  writeReg B (← (undefined_bool ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
