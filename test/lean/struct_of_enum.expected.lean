import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

inductive e_test where | VAL
  deriving Inhabited, DecidableEq

open e_test


structure s_test where
  f : e_test

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def undefined_e_test (_ : Unit) : SailM e_test := do
  (internal_pick [VAL])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def e_test_of_num (arg_ : Nat) : e_test :=
  match arg_ with
  | _ => VAL

def num_of_e_test (arg_ : e_test) : Int :=
  match arg_ with
  | VAL => 0

def undefined_s_test (_ : Unit) : SailM s_test := do
  (pure { f := (← (undefined_e_test ())) })

def initialize_registers (_ : Unit) : Unit :=
  ()

