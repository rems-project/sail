import Out.Sail.Sail

open Sail

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

open RegisterRef
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
abbrev SailM := PreSailM RegisterType trivialChoiceSource

def test (_ : Unit) : SailM Int := do
  writeReg INT (HAdd.hAdd (← readReg INT) 1)
  readReg INT

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R0 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg INT (← (undefined_int ()))
  writeReg BOOL (← (undefined_bool ()))
  writeReg NAT (← (undefined_nat ()))
  writeReg BIT (← (undefined_bit ()))

