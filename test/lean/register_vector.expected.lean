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

abbrev reg_index := Nat

inductive Register : Type where
  | R0
  | R1
  | R2
  | R3
  | R4
  | R5
  | R6
  | R7
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  | R16
  | R17
  | R18
  | R19
  | R20
  | R21
  | R22
  | R23
  | R24
  | R25
  | R26
  | R27
  | R28
  | R29
  | R30
  | _PC
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .R0 => (BitVec 64)
  | .R1 => (BitVec 64)
  | .R2 => (BitVec 64)
  | .R3 => (BitVec 64)
  | .R4 => (BitVec 64)
  | .R5 => (BitVec 64)
  | .R6 => (BitVec 64)
  | .R7 => (BitVec 64)
  | .R8 => (BitVec 64)
  | .R9 => (BitVec 64)
  | .R10 => (BitVec 64)
  | .R11 => (BitVec 64)
  | .R12 => (BitVec 64)
  | .R13 => (BitVec 64)
  | .R14 => (BitVec 64)
  | .R15 => (BitVec 64)
  | .R16 => (BitVec 64)
  | .R17 => (BitVec 64)
  | .R18 => (BitVec 64)
  | .R19 => (BitVec 64)
  | .R20 => (BitVec 64)
  | .R21 => (BitVec 64)
  | .R22 => (BitVec 64)
  | .R23 => (BitVec 64)
  | .R24 => (BitVec 64)
  | .R25 => (BitVec 64)
  | .R26 => (BitVec 64)
  | .R27 => (BitVec 64)
  | .R28 => (BitVec 64)
  | .R29 => (BitVec 64)
  | .R30 => (BitVec 64)
  | ._PC => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg _PC
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.RegisterVector

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open Register

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg _PC (← (undefined_bitvector 64))
  writeReg R30 (← (undefined_bitvector 64))
  writeReg R29 (← (undefined_bitvector 64))
  writeReg R28 (← (undefined_bitvector 64))
  writeReg R27 (← (undefined_bitvector 64))
  writeReg R26 (← (undefined_bitvector 64))
  writeReg R25 (← (undefined_bitvector 64))
  writeReg R24 (← (undefined_bitvector 64))
  writeReg R23 (← (undefined_bitvector 64))
  writeReg R22 (← (undefined_bitvector 64))
  writeReg R21 (← (undefined_bitvector 64))
  writeReg R20 (← (undefined_bitvector 64))
  writeReg R19 (← (undefined_bitvector 64))
  writeReg R18 (← (undefined_bitvector 64))
  writeReg R17 (← (undefined_bitvector 64))
  writeReg R16 (← (undefined_bitvector 64))
  writeReg R15 (← (undefined_bitvector 64))
  writeReg R14 (← (undefined_bitvector 64))
  writeReg R13 (← (undefined_bitvector 64))
  writeReg R12 (← (undefined_bitvector 64))
  writeReg R11 (← (undefined_bitvector 64))
  writeReg R10 (← (undefined_bitvector 64))
  writeReg R9 (← (undefined_bitvector 64))
  writeReg R8 (← (undefined_bitvector 64))
  writeReg R7 (← (undefined_bitvector 64))
  writeReg R6 (← (undefined_bitvector 64))
  writeReg R5 (← (undefined_bitvector 64))
  writeReg R4 (← (undefined_bitvector 64))
  writeReg R3 (← (undefined_bitvector 64))
  writeReg R2 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg R0 (← (undefined_bitvector 64))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
