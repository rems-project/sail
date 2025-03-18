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

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

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

namespace Functions

/-- Type quantifiers: x : Nat, 0 ≤ x ∧ x ≤ 31 -/
def f_int (x : Nat) : Int :=
  0

/-- Type quantifiers: x : Nat, 0 ≤ x ∧ x ≤ 31 -/
def f_nat (x : Nat) : Nat :=
  0

/-- Type quantifiers: x : Nat, k_n : Nat, 0 ≤ x ∧ x ≤ k_n -/
def f_negvar (x : Nat) : Int :=
  x

/-- Type quantifiers: x : Nat, k_n : Nat, 0 ≤ x ∧ x ≤ k_n -/
def f_nnegvar (x : Nat) : Nat :=
  x

/-- Type quantifiers: x : Int, k_n : Int, k_m : Int, k_n ≤ x ∧ x ≤ k_m -/
def f_unkn (x : Int) : Int :=
  x

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
