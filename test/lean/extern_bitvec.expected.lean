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

def extern_const (_ : Unit) : (BitVec 64) :=
  (0xFFFF000012340000 : (BitVec 64))

def extern_add (_ : Unit) : (BitVec 16) :=
  ((0xFFFF : (BitVec 16)) + (0x1234 : (BitVec 16)))

def extern_replicate_bits (_ : Unit) : (BitVec 64) :=
  (BitVec.replicateBits (0x1234 : (BitVec 16)) 4)

def extern_slice (x : (BitVec 16)) : (BitVec 4) :=
  (BitVec.slice x 2 4)

def extern_vector_length (x : (Vector Int 3)) : Int :=
  (Vector.length x)

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())


end Out.Functions
