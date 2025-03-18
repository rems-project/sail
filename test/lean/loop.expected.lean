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
  | r
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r => Nat

instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg r
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

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loop (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let res := loop_vars
    loop_vars := (res +i 1)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  let loop_i_lower := n
  let loop_i_upper := m
  let mut loop_vars := ()
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let () := loop_vars
    loop_vars ← do writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res ← (( do
    let loop_i_lower := n
    let loop_i_upper := m
    let mut loop_vars := res
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let res := loop_vars
      loop_vars ← do
        let res : Nat := (res +i 1)
        writeReg r ((← readReg r) +i res)
        (pure res)
    (pure loop_vars) ) : SailM Nat )
  (pure (res +i 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopmultiplevar (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) ← (( do
    let loop_i_lower := m
    let loop_i_upper := n
    let mut loop_vars := (mult, res)
    for i in [loop_i_lower:loop_i_upper + 1:1]i do
      let (mult, res) := loop_vars
      loop_vars :=
        let res : Nat := (res +i 1)
        let mult : Nat := (res *i mult)
        (mult, res)
    (pure loop_vars) ) : Id (Nat × Nat) )
  (pure mult)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def foreach_loopuseindex (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let loop_i_lower := m
  let loop_i_upper := n
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper + 1:1]i do
    let res := loop_vars
    loop_vars := (res +i i)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loop (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mut loop_vars := res
  while (λ res => (res <b n)) loop_vars do
    let res := loop_vars
    loop_vars := ((res +i 1) : Nat)
  (pure loop_vars)

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmon (m : Nat) (n : Nat) : SailM Nat := do
  let mut loop_vars := ()
  while (← (λ _ => do (pure ((← readReg r) <b n))) loop_vars) do
    let () := loop_vars
    loop_vars ← do writeReg r ((← readReg r) +i 1)
  (pure loop_vars)
  readReg r

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopboth (m : Nat) (n : Nat) : SailM Nat := do
  let res : Nat := 0
  let res ← (( do
    let mut loop_vars := res
    while (λ res => (res <b n)) loop_vars do
      let res := loop_vars
      loop_vars ← do
        let res : Nat := (res +i 1)
        writeReg r ((← readReg r) +i res)
        (pure res)
    (pure loop_vars) ) : SailM Nat )
  (pure (res +i 1))

/-- Type quantifiers: n : Nat, m : Nat, 0 ≤ m, 0 ≤ n -/
def while_loopmultiplevar (m : Nat) (n : Nat) : Nat := Id.run do
  let res : Nat := 0
  let mult : Nat := 1
  let (mult, res) ← (( do
    let mut loop_vars := (mult, res)
    while (λ (mult, res) => (res <b n)) loop_vars do
      let (mult, res) := loop_vars
      loop_vars :=
        (let res : Nat := (res +i 1)
        let mult : Nat := (res *i mult)
        (mult, res) : (Nat × Nat))
    (pure loop_vars) ) : Id (Nat × Nat) )
  (pure mult)

def while_print (_ : Unit) : Unit := Id.run do
  let i : Int := 0
  let i ← (( do
    let mut loop_vars := i
    while (λ i => (i <b 10)) loop_vars do
      let i := loop_vars
      loop_vars := ((i +i 1) : Int)
    (pure loop_vars) ) : Id Int )
  (pure (print_int "i = " i))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r (← (undefined_nat ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Functions
