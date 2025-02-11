import Out.Sail.Sail

open Sail

inductive Register : Type where
  | B
  | R
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .B => Bool
  | .R => Nat

open RegisterRef
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg B
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg R
abbrev SailM := PreSailM RegisterType trivialChoiceSource

/-- Type quantifiers: n : Nat, 0 ≤ n -/
def elif (n : Nat) : (BitVec 1) :=
  if (Eq n 0)
  then 1#1
  else if (Eq n 1)
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
  let b := (Eq n 0)
  if b
  then writeReg R n
       writeReg B b
  else writeReg B b

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R (← (undefined_nat ()))
  writeReg B (← (undefined_bool ()))

