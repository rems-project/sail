import Out.Sail.Sail

open Sail

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

open RegisterRef
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg _PC
abbrev SailM := PreSailM RegisterType

def GPRs : (Vector (RegisterRef RegisterType (BitVec 64)) 31) :=
  #v[Reg R30, Reg R29, Reg R28, Reg R27, Reg R26, Reg R25, Reg R24, Reg R23, Reg R22, Reg R21,
    Reg R20, Reg R19, Reg R18, Reg R17, Reg R16, Reg R15, Reg R14, Reg R13, Reg R12, Reg R11,
    Reg R10, Reg R9, Reg R8, Reg R7, Reg R6, Reg R5, Reg R4, Reg R3, Reg R2, Reg R1, Reg R0]

/-- Type quantifiers: n : Int, 0 ≤ n ∧ n ≤ 31 -/
def wX (n : Nat) (value : (BitVec 64)) : SailM Unit := do
  if (Ne n 31)
  then writeRegRef (vectorAccess GPRs n) value
  else (pure ())

/-- Type quantifiers: n : Int, 0 ≤ n ∧ n ≤ 31 -/
def rX (n : Nat) : SailM (BitVec 64) := do
  if (Ne n 31)
  then (reg_deref (vectorAccess GPRs n))
  else (pure (0x0000000000000000 : (BitVec 64)))

def rPC (lit : Unit) : SailM (BitVec 64) := do
  readReg _PC

def wPC (pc : (BitVec 64)) : SailM Unit := do
  writeReg _PC pc

/-- Type quantifiers: r : Int, 0 ≤ r ∧ r ≤ 31 -/
def monad_test (r : Nat) : SailM (BitVec 1) := do
  if (Eq (← (rX r)) (0x0000000000000000 : (BitVec 64)))
  then (pure 1#1)
  else if (Eq (← (rX r)) (0x0000000000000001 : (BitVec 64)))
       then (pure 1#1)
       else (pure 0#1)

def initialize_registers (lit : Unit) : SailM Unit := do
  writeReg _PC sorry
  writeReg R30 sorry
  writeReg R29 sorry
  writeReg R28 sorry
  writeReg R27 sorry
  writeReg R26 sorry
  writeReg R25 sorry
  writeReg R24 sorry
  writeReg R23 sorry
  writeReg R22 sorry
  writeReg R21 sorry
  writeReg R20 sorry
  writeReg R19 sorry
  writeReg R18 sorry
  writeReg R17 sorry
  writeReg R16 sorry
  writeReg R15 sorry
  writeReg R14 sorry
  writeReg R13 sorry
  writeReg R12 sorry
  writeReg R11 sorry
  writeReg R10 sorry
  writeReg R9 sorry
  writeReg R8 sorry
  writeReg R7 sorry
  writeReg R6 sorry
  writeReg R5 sorry
  writeReg R4 sorry
  writeReg R3 sorry
  writeReg R2 sorry
  writeReg R1 sorry
  writeReg R0 sorry

