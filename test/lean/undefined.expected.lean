import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: n : Int -/
def foo (n : Int) : SailM (Bool × (BitVec 1) × Int × Nat × (BitVec 3)) := do
  (pure ((← (undefined_bool ())), (← (undefined_bit ())), (← (undefined_int ())), (← (undefined_nat
        ())), (← (undefined_bitvector 3))))

def initialize_registers (_ : Unit) : Unit :=
  ()

