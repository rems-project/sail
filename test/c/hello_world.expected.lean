import Out.Sail.Sail
import Out.Sail.BitVec

open Sail

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource

def sail_main (_ : Unit) : SailM Unit := do
  (print_endline_effect "Hello, World!")

def initialize_registers (_ : Unit) : Unit :=
  ()

def main (_ : List String) : IO UInt32 := do
  main_of_sail_main ⟨default, (), default, default, default⟩ sail_main
  return 0
