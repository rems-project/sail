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
  | BIT
  | NAT
  | BOOL
  | INT
  | R1
  | R0
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .BIT => (BitVec 1)
  | .NAT => Nat
  | .BOOL => Bool
  | .INT => Int
  | .R1 => (BitVec 64)
  | .R0 => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg BIT
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg R0
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg BOOL
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg INT
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg NAT
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

def test (_ : Unit) : SailM Int := do
  writeReg INT ((← readReg INT) +i 1)
  readReg INT

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R0 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg INT (← (undefined_int ()))
  writeReg BOOL (← (undefined_bool ()))
  writeReg NAT (← (undefined_nat ()))
  writeReg BIT (← (undefined_bit ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Functions
