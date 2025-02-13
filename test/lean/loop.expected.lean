import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

inductive Register : Type where
  | r
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r => Int

open RegisterRef
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg r
abbrev SailM := PreSailM RegisterType trivialChoiceSource

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloop (m : Nat) (n : Nat) : Int :=
  let res : Int := 0
  let loop_i_lower := m
  let loop_i_upper := n
  (foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (HAdd.hAdd res 1)))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopmon (m : Nat) (n : Nat) : SailM Int := do
  let loop_i_lower := n
  let loop_i_upper := m
  (foreach_M loop_i_lower loop_i_upper 1 ()
    (λ i _ => do (writeReg r (HAdd.hAdd (← readReg r) 1) : SailM Unit)))
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopboth (m : Nat) (n : Nat) : SailM Int := do
  let res : Int := 0
  let res : Int ← do
    let loop_i_lower := n
    let loop_i_upper := m
    (foreach_M loop_i_lower loop_i_upper 1 res
      (λ i res => do
        let res : Int := (HAdd.hAdd res 1)
        writeReg r (HAdd.hAdd (← readReg r) res)
        (pure res)))
  (pure (HAdd.hAdd res 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopmultiplevar (m : Nat) (n : Nat) : Int :=
  let res : Int := 0
  let mult : Int := 1
  let (mult, res) :=
    let loop_i_lower := m
    let loop_i_upper := n
    (foreach_ loop_i_lower loop_i_upper 1 (mult, res)
      (λ i (mult, res) =>
        let res : Int := (HAdd.hAdd res 1)
        let mult : Int := (HMul.hMul res mult)
        (mult, res)))
  mult

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreachloopuseindex (m : Nat) (n : Nat) : Nat :=
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  (foreach_ loop_i_lower loop_i_upper 1 res (λ i res => (HAdd.hAdd res i)))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r (← (undefined_int ()))

