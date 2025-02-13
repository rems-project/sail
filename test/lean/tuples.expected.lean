import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def let0 := (20, 300000000000000000000000)

def y :=
  let (y, z) := let0
  y

def z :=
  let (y, z) := let0
  z

def tuple1 (_ : Unit) : (Int × Int × ((BitVec 2) × Unit)) :=
  (3, 5, ((0b10 : (BitVec 2)), ()))

def tuple2 (_ : Unit) : SailM (Int × Int) := do
  (pure ((← (undefined_int ())), (← (undefined_int ()))))

def initialize_registers (_ : Unit) : Unit :=
  ()

