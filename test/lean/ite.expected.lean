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

import Out.String

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

open option
open Register

namespace Functions

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def elif (n : Nat) : (BitVec 1) :=
  if (BEq.beq n 0)
  then 1#1
  else
    if (BEq.beq n 1)
    then 1#1
    else 0#1

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def monadic_in_out (n : Nat) : SailM Nat := do
  if (← readReg B)
  then writeReg R n
  else (pure ())
  readReg R

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def monadic_lines (n : Nat) : SailM Unit := do
  let b := (BEq.beq n 0)
  if b
  then
    writeReg R n
    writeReg B b
  else writeReg B b

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R (← (undefined_nat ()))
  writeReg B (← (undefined_bool ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Functions
