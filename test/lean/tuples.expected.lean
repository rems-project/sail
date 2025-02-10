import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def tuple1 (lit : Unit) : (Int × Int × ((BitVec 2) × Unit)) :=
  (3, 5, ((0b10 : (BitVec 2)), ()))

def tuple2 (lit : Unit) : SailM (Int × Int) := do
  (pure ((← (undefined_int ())), (← (undefined_int ()))))

def initialize_registers (lit : Unit) : Unit :=
  ()

