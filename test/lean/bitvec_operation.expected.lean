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

def bitvector_eq (x : (BitVec 16)) (y : (BitVec 16)) : Bool :=
  (BEq.beq x y)

def bitvector_neq (x : (BitVec 16)) (y : (BitVec 16)) : Bool :=
  (bne x y)

def bitvector_len (x : (BitVec 16)) : Nat :=
  (Sail.BitVec.length x)

def bitvector_sign_extend (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.signExtend x 32)

def bitvector_zero_extend (x : (BitVec 16)) : (BitVec 32) :=
  (Sail.BitVec.zeroExtend x 32)

def bitvector_truncate (x : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.truncate x 16)

def bitvector_truncateLSB (x : (BitVec 32)) : (BitVec 16) :=
  (Sail.BitVec.truncateLsb x 16)

def bitvector_append (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 32) :=
  (x ++ y)

def bitvector_add (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (x + y)

def bitvector_sub (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (x - y)

def bitvector_not (x : (BitVec 16)) : (BitVec 16) :=
  (Complement.complement x)

def bitvector_and (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (x &&& y)

def bitvector_or (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (x ||| y)

def bitvector_xor (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (x ^^^ y)

def bitvector_unsigned (x : (BitVec 16)) : Nat :=
  (BitVec.toNat x)

def bitvector_signed (x : (BitVec 16)) : Int :=
  (BitVec.toInt x)

/-- Type quantifiers: i : Nat, 0 ≤ i ∧ i ≤ 15 -/
def bitvector_access' (x : (BitVec 16)) (i : Nat) : (BitVec 1) :=
  (BitVec.access x i)

/-- Type quantifiers: i : Int -/
def bitvector_plus_int (x : (BitVec 16)) (i : Int) : (BitVec 16) :=
  (BitVec.addInt x i)

def bitvector_literal (x : (BitVec 1)) (y : (BitVec 1)) : (BitVec 2) :=
  (BitVec.join1 [x, y])

/-- Type quantifiers: y : Int, x : Int -/
def vector_literal (x : Int) (y : Int) : (Vector Int 2) :=
  #v[y, x]

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
