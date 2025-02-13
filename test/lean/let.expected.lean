import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def foo (_ : Unit) : (BitVec 16) :=
  let z := (HOr.hOr (0xFFFF : (BitVec 16)) (0xABCD : (BitVec 16)))
  (HAnd.hAnd (0x0000 : (BitVec 16)) z)

def bar (_ : Unit) : (BitVec 16) :=
  let z : (BitVec 16) := (HOr.hOr (0xFFFF : (BitVec 16)) (0xABCD : (BitVec 16)))
  (HAnd.hAnd (0x0000 : (BitVec 16)) z)

def baz (_ : Unit) : SailM (BitVec 16) := do
  (print_effect "baz")
  (pure (0x0000 : (BitVec 16)))

def initialize_registers (_ : Unit) : Unit :=
  ()

