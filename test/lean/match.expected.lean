import Out.Sail.Sail

open Sail

inductive E where | A | B | C
  deriving Inhabited, DecidableEq

open E

inductive Register : Type where
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r_C => E
  | .r_B => E
  | .r_A => E

open RegisterRef
instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
abbrev SailM := PreSailM RegisterType trivialChoiceSource

def undefined_E (lit : Unit) : SailM E := do
  (internal_pick [A, B, C])

def match_enum (x : E) : (BitVec 1) :=
  match x with
  | A => 1#1
  | B => 1#1
  | C => 0#1

def match_option (x : (Option (BitVec 1))) : (BitVec 1) :=
  match x with
  | some x => x
  | none => 0#1

/-- Type quantifiers: y : Int, x : Int -/
def match_pair_pat (x : Int) (y : Int) : Int :=
  match (x, y) with
  | (a, b) => (HAdd.hAdd a b)

/-- Type quantifiers: arg1 : Int, arg0 : Int -/
def match_pair (arg0 : Int) (arg1 : Int) : Int :=
  let x := (arg0, arg1)
  match x with
  | (a, b) => (HAdd.hAdd a b)

def match_reg (x : E) : SailM E := do
  match x with
  | A => readReg r_A
  | B => readReg r_B
  | C => readReg r_C

def initialize_registers (lit : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))

