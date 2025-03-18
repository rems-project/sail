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

inductive virtaddr where
  | virtaddr (_ : (BitVec 32))
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

open virtaddr
open option

namespace Functions

/-- Type quantifiers: n : Nat, n > 0 -/
def foo (n : Nat) : (BitVec 4) :=
  (0xF : (BitVec 4))

/-- Type quantifiers: n : Nat, n > 0 -/
def foo2 (n : Nat) : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: k_n : Int -/
def bar (x : (BitVec k_n)) : (BitVec k_n) :=
  x

def two_tuples (tuple_0 : (String × String)) (tuple_1 : (String × String)) : String :=
  let (x, y) := tuple_0
  let (z, t) := tuple_1
  y

/-- Type quantifiers: tuple_0.2 : Nat, tuple_0.2 ≥ 0 -/
def two_tuples_atom (tuple_0 : (String × Nat)) (tuple_1 : (String × String)) : (BitVec tuple_0.2) :=
  let (x, y) := tuple_0
  let (z, t) := tuple_1
  (BitVec.zero y)

def tuple_of_tuple (tuple_0 : (String × String)) : String :=
  let (s1, s2) := tuple_0
  s1

def use_tuple_of_tuple (s : String) : String :=
  (tuple_of_tuple (s, s))

/-- Type quantifiers: k_nn : Nat, k_nn > 0 -/
def hex_bits_signed2_forwards (bv : (BitVec k_nn)) : (Nat × String) :=
  let len := (Sail.BitVec.length bv)
  let s :=
    if (BEq.beq (BitVec.access bv (len -i 1)) 1#1)
    then "stub1"
    else "stub2"
  ((Sail.BitVec.length bv), s)

/-- Type quantifiers: k_nn : Nat, k_nn > 0 -/
def hex_bits_signed2_forwards_matches (bv : (BitVec k_nn)) : Bool :=
  true

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_signed2_backwards (tuple_0 : (Nat × String)) : (BitVec tuple_0.1) :=
  let (notn, str) := tuple_0
  if (BEq.beq str "-")
  then (BitVec.zero notn)
  else
    let parsed := (BitVec.zero notn)
    if (BEq.beq (BitVec.access parsed (notn -i 1)) 0#1)
    then parsed
    else (BitVec.zero notn)

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_signed2_backwards_matches (tuple_0 : (Nat × String)) : Bool :=
  let (n, str) := tuple_0
  true

def test_constr (app_0 : virtaddr) : (BitVec 32) :=
  let .virtaddr addr := app_0
  addr

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def termination (n : Nat) : Int :=
  if (BEq.beq n 0)
  then 0
  else (1 +i (termination (n -i 1)))

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
