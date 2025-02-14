import Out.Sail.Sail
import Out.Sail.BitVec

open Sail


inductive exception where
  | E_bool (_ : Bool)
  | E_unit (_ : Unit)

open exception

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource exception

def prop (_ : Unit) : SailM Bool := do
  sailTryCatch (sailThrow ((E_bool true))) (fun the_exception => 
  match the_exception with
  | E_bool b => (pure b)
  | E_unit () => (pure false))

def initialize_registers (_ : Unit) : Unit :=
  ()

