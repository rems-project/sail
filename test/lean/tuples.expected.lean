import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail


abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Defs

import Out.Specialization

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail



namespace Functions

def let0 := (20, 300000000000000000000000)

def y :=
  let (y, z) := let0
  y

def z :=
  let (y, z) := let0
  z

def tuple1 (_ : Unit) : (Int × Int × ((BitVec 2) × Unit)) :=
  (3, 5, ((0b10 : (BitVec 2)), ()))

def tuple2 (_ : Unit) : SailM (Int × Int) := do
  (pure ((← (undefined_int ())), (← (undefined_int ()))))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
open Functions

