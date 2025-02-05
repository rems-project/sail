import Out.Sail.Sail

open Sail

inductive e_test where | VAL
  deriving Inhabited, DecidableEq

open e_test


structure s_test where
  f : e_test

abbrev SailM := StateM Unit

def undefined_e_test (lit : Unit) : SailM e_test := do
  sorry

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 0 -/
def e_test_of_num (arg_ : Nat) : e_test :=
  match arg_ with
  | _ => VAL

def num_of_e_test (arg_ : e_test) : Int :=
  match arg_ with
  | VAL => 0

def undefined_s_test (lit : Unit) : SailM s_test := do
  (pure { f := (← (undefined_e_test ())) })

def initialize_registers (lit : Unit) : Unit :=
  ()

