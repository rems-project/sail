import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.String

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option

def foo (_ : Unit) : (BitVec 16) :=
  let z := ((0xFFFF : (BitVec 16)) ||| (0xABCD : (BitVec 16)))
  ((0x0000 : (BitVec 16)) &&& z)

def bar (_ : Unit) : (BitVec 16) :=
  let z : (BitVec 16) := ((0xFFFF : (BitVec 16)) ||| (0xABCD : (BitVec 16)))
  ((0x0000 : (BitVec 16)) &&& z)

def baz (_ : Unit) : SailM (BitVec 16) := do
  (print_effect "baz")
  (pure (0x0000 : (BitVec 16)))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())


end Out.Functions
