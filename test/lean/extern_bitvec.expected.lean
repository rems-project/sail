import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def extern_const (lit : Unit) : (BitVec 64) :=
  (0xFFFF000012340000 : (BitVec 64))

def extern_add (lit : Unit) : (BitVec 16) :=
  (HAdd.hAdd (0xFFFF : (BitVec 16)) (0x1234 : (BitVec 16)))

def initialize_registers (lit : Unit) : Unit :=
  ()

