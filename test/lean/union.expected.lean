import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

structure rectangle where
  width : Int
  height : Int
  deriving Inhabited, BEq

structure circle where
  radius : Int
  deriving Inhabited, BEq

inductive shape where
  | Rectangle (_ : rectangle)
  | Circle (_ : circle)
  deriving Inhabited, BEq

/-- Type quantifiers: k_a : Type -/
inductive my_option (k_a : Type) where
  | MySome (_ : k_a)
  | MyNone (_ : Unit)
  deriving Inhabited, BEq

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Union

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open shape
open my_option

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())


end Out.Functions
