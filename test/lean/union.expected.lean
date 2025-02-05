import Out.Sail.Sail

open Sail


structure rectangle where
  width : Int
  height : Int


structure circle where
  radius : Int


inductive shape where
  | Rectangle (_ : rectangle)
  | Circle (_ : circle)

open shape

/-- Type quantifiers: k_a : Type -/

inductive my_option (k_a : Type) where
  | MySome (_ : k_a)
  | MyNone (_ : Unit)

open my_option

abbrev SailM := StateM Unit

def undefined_rectangle (lit : Unit) : SailM rectangle := do
  (pure { width := sorry
          height := sorry })

def undefined_circle (lit : Unit) : SailM circle := do
  (pure { radius := sorry })

/-- Type quantifiers: k_a : Type -/
def is_none (opt : my_option k_a) : Bool :=
  match opt with
  | MySome _ => false
  | MyNone () => true

/-- Type quantifiers: k_a : Type -/
def use_is_none (opt : my_option k_a) : Bool :=
  (is_none opt)

def initialize_registers (lit : Unit) : Unit :=
  ()

