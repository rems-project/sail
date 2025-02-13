import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

inductive E where | A | B | C
  deriving Inhabited, DecidableEq

open E

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def undefined_E (_ : Unit) : SailM E := do
  (internal_pick [A, B, C])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 2 -/
def E_of_num (arg_ : Nat) : E :=
  match arg_ with
  | 0 => A
  | 1 => B
  | _ => C

def num_of_E (arg_ : E) : Int :=
  match arg_ with
  | A => 0
  | B => 1
  | C => 2

def initialize_registers (_ : Unit) : Unit :=
  ()

