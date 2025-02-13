import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: n : Int -/
def foo (n : Int) : SailM (Bool × (BitVec 1) × Int × Nat × (BitVec 3)) := do
  (pure ((← (undefined_bool ())), (← (undefined_bit ())), (← (undefined_int ())), (← (undefined_nat
        ())), (← (undefined_bitvector 3))))

/-- Type quantifiers: n : Int -/
def bar (n : Int) : SailM (Vector Int 4) := do
  (undefined_vector 4 n)

def initialize_registers (_ : Unit) : Unit :=
  ()

