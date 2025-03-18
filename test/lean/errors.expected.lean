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

import Out.String

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

open option
open Register

namespace Functions

/-- Type quantifiers: k_ex824# : Bool -/
def test_exit (b : Bool) : SailM Unit := do
  if b
  then throw Error.Exit
  else (pure ())

/-- Type quantifiers: k_ex826# : Bool -/
def test_assert (b : Bool) : SailM (BitVec 1) := do
  assert b "b is false"
  (pure 1#1)

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg dummy (← (undefined_bit ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Functions
