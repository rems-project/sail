import Sail.sail

structure My_struct  where
  field1 : Int
  field2 : Int


def undefined_My_struct (lit : Unit) : My_struct :=
  sorry /- internal plet -/

def initialize_registers : Unit :=
  ()

