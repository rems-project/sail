import Out.Sail.Sail

open Sail

inductive E where | A | B | C
  deriving Inhabited
open E

def undefined_E : SailM E := do
  sorry

def initialize_registers : Unit :=
  ()

