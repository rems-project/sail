import Out.Sail.Sail

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def extern_const (_ : Unit) : (BitVec 64) :=
  (0xFFFF000012340000 : (BitVec 64))

def extern_add (_ : Unit) : (BitVec 16) :=
  (HAdd.hAdd (0xFFFF : (BitVec 16)) (0x1234 : (BitVec 16)))

def initialize_registers (_ : Unit) : Unit :=
  ()

