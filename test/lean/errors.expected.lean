import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

inductive Register : Type where
  | dummy
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .dummy => (BitVec 1)

open RegisterRef
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg dummy
abbrev SailM := PreSailM RegisterType trivialChoiceSource

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

