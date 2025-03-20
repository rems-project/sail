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

abbrev xlen : Int := 64

abbrev xlen_bytes : Int := 8

abbrev xlenbits := (BitVec 64)

abbrev regbits := (BitVec 5)

inductive iop where | RISCV_ADDI | RISCV_SLTI | RISCV_SLTIU | RISCV_XORI | RISCV_ORI | RISCV_ANDI
  deriving Inhabited, BEq

inductive ast where
  | ITYPE (_ : ((BitVec 12) × regbits × regbits × iop))
  | LOAD (_ : ((BitVec 12) × regbits × regbits))
  deriving Inhabited, BEq

inductive Register : Type where
  | Xs
  | nextPC
  | PC
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .Xs => (Vector (BitVec 64) 32)
  | .nextPC => (BitVec 64)
  | .PC => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg PC
instance : Inhabited (RegisterRef RegisterType (Vector (BitVec 64) 32)) where
  default := .Reg Xs
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.RiscvDuopod

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open iop
open ast
open Register

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg PC (← (undefined_bitvector 64))
  writeReg nextPC (← (undefined_bitvector 64))
  writeReg Xs (← (undefined_vector 32 (← (undefined_bitvector 64))))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
