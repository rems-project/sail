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

inductive E where | A | B | C
  deriving Inhabited, BEq

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

instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.String

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option
open Register
open E

def undefined_E (_ : Unit) : SailM E := do
  (internal_pick [A, B, C])

def match_enum (x : E) : (BitVec 1) :=
  match x with
  | A => 1#1
  | B => 1#1
  | C => 0#1

def match_option (x : (Option (BitVec 1))) : (BitVec 1) :=
  match x with
  | .some x => x
  | none => 0#1

/-- Type quantifiers: y : Int, x : Int -/
def match_pair_pat (x : Int) (y : Int) : Int :=
  match (x, y) with
  | (a, b) => (a +i b)

/-- Type quantifiers: arg1 : Int, arg0 : Int -/
def match_pair (arg0 : Int) (arg1 : Int) : Int :=
  let x := (arg0, arg1)
  match x with
  | (a, b) => (a +i b)

def match_reg (x : E) : SailM E := do
  match x with
  | A => readReg r_A
  | B => readReg r_B
  | C => readReg r_C

/-- Type quantifiers: y : Int -/
def match_let (x : E) (y : Int) : SailM Int := do
  match x with
  | A =>
    let x := (y +i y)
    let z ← do (pure ((y +i y) +i (← (undefined_int ()))))
    (pure (z +i x))
  | B => (pure 42)
  | C => (pure 23)

def match_read (x : E) : SailM Unit := do
  writeReg r_A (← do
    match x with
    | A => readReg r_A
    | B => readReg r_B
    | C => readReg r_C)

def const16 (_ : Unit) : ((BitVec 16) × Bool) :=
  ((0xFFFF : (BitVec 16)), true)

def const32 (_ : Unit) : ((BitVec 32) × Bool) :=
  ((0xEEEEEEEE : (BitVec 32)), false)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def match_width (x : (BitVec k_n)) : (BitVec (2 * k_n)) :=
  let (foo, _) : ((BitVec k_n) × Bool) :=
    match (Sail.BitVec.length x) with
    | 16 => (const16 ())
    | 32 => (const32 ())
    | n => ((BitVec.zero n), false)
  (foo ++ foo)

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())


end Out.Functions
