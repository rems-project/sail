import Out.Sail.Sail

open Sail

abbrev SailM := StateM Unit

def foo (lit : Unit) : Bool :=
  true

def initialize_registers (lit : Unit) : Unit :=
  ()

