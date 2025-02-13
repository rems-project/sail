import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

/-- Type quantifiers: k_n : Int, m : Int, m ≥ k_n -/
def EXTZ {m : _} (v : (BitVec k_n)) : (BitVec m) :=
  (Sail.BitVec.zeroExtend v m)

def foo (x : (BitVec 8)) : (BitVec 16) :=
  (EXTZ x)

/-- Type quantifiers: k_ex868# : Bool, n : Nat, n ≥ 0 -/
def slice_mask2 {n : _} (i : (BitVec n)) (l : (BitVec n)) (b : Bool) : (BitVec n) :=
  if b
  then i
  else let one : (BitVec n) := (EXTZ l)
       (HAdd.hAdd one one)

def initialize_registers (_ : Unit) : Unit :=
  ()

