import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def EXTZ {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

def foo (x : (BitVec 8)) : (BitVec 16) :=
  (EXTZ x)

def initialize_registers (_ : Unit) : Unit :=
  ()

