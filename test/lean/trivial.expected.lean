import Out.Sail.Sail

open Sail

abbrev SailM := StateM Unit

def foo (y : Unit) : Unit :=
  y

def initialize_registers (lit : Unit) : Unit :=
  ()

