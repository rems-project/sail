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

inductive E where | A | B | C
  deriving Inhabited, BEq

inductive Register : Type where
  | r
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r => Nat
  | .r_C => E
  | .r_B => E
  | .r_A => E

instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg r
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.EarlyReturn

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open Register
open E

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))
  writeReg r (← (undefined_nat ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
