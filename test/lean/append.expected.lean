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

open option

namespace Functions

def unif_bitvec_append (x : (BitVec 13)) (y : (BitVec 3)) : (BitVec (4 * 4)) :=
  (x ++ y)

def unif_bitvec_replicate (x : (BitVec 4)) : (BitVec (2 * 8)) :=
  (BitVec.replicateBits x 4)

def unif_subrange_bits (x : (BitVec 16)) : (BitVec (17 - 10 + 1)) :=
  (Sail.BitVec.extractLsb x 10 3)

/-- Type quantifiers: i : Nat, i ≥ 0 -/
def unif_vector_subrange (i : Nat) (v : (BitVec (8 * i + 8))) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v ((8 *i i) +i 7) (8 *i i))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
