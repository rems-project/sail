import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

structure rectangle where
  width : Int
  height : Int
  deriving BEq, Inhabited, Repr

structure circle where
  radius : Int
  deriving BEq, Inhabited, Repr

inductive shape where
  | Rectangle (_ : rectangle)
  | Circle (_ : circle)
  deriving Inhabited, BEq, Repr
  open shape

/-- Type quantifiers: k_a : Type -/
inductive my_option (k_a : Type) where
  | MySome (_ : k_a)
  | MyNone (_ : Unit)
  deriving Inhabited, BEq, Repr
  open my_option

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Sail.IntRange
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

namespace Out.Functions

open shape
open my_option

def undefined_rectangle (_ : Unit) : SailM rectangle := do
  (pure { width := ← (undefined_int ())
          height := ← (undefined_int ()) })

def undefined_circle (_ : Unit) : SailM circle := do
  (pure { radius := ← (undefined_int ()) })

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (my_option k_a)) : Bool :=
  match opt with
  | .MySome _ => false
  | .MyNone () => true

/-- Type quantifiers: k_a : Type -/
def use_is_none (opt : (my_option k_a)) : Bool :=
  (is_none opt)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
