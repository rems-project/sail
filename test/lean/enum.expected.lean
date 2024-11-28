import Sail.sail

inductive E where | A | B | C
  deriving Inhabited

def undefined_E : E :=
  (sorry : E)

def initialize_registers : Unit :=
  ()

