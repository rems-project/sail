import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

namespace Defs

abbrev bit := (BitVec 1)

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception


XXXXXXXXX

import Sail
import Out.Defs
import Out.Specialization
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

open ConcurrencyInterfaceV1

open Defs
namespace Functions

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: n : Int -/
def foo (n : Int) : SailM (Bool × (BitVec 1) × Int × Nat × (BitVec 3)) := do
  (pure ((← (undefined_bool ())), (← (undefined_bit ())), (← (undefined_int ())), (← (undefined_nat
        ())), (← (undefined_bitvector 3))))

/-- Type quantifiers: n : Int -/
def bar (n : Int) : SailM (Vector Int 4) := do
  (undefined_vector 4 n)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Out.Functions
