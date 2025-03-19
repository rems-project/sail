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

def decode (v__0 : (BitVec 32)) : Bool :=
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 31 24) (0xF8 : (BitVec 8)))
       (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 21 21) (0b1 : (BitVec 1)))
         (BEq.beq (Sail.BitVec.extractLsb v__0 11 10) (0b10 : (BitVec 2)))))
  then
    let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
    let Rm : (BitVec 5) := (Sail.BitVec.extractLsb v__0 20 16)
    if (BEq.beq Rm Rn)
    then true
    else false
  else
    if (BEq.beq (Sail.BitVec.extractLsb v__0 30 24) (0b1001010 : (BitVec 7)))
    then
      let Rn : (BitVec 5) := (Sail.BitVec.extractLsb v__0 9 5)
      let Rd : (BitVec 5) := (Sail.BitVec.extractLsb v__0 4 0)
      if (BEq.beq Rn Rd)
      then true
      else false
    else
      if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__0 31 12) (0xD5033 : (BitVec 20)))
           (BEq.beq (Sail.BitVec.extractLsb v__0 7 0) (0xBF : (BitVec 8))))
      then true
      else
        if (BEq.beq (Sail.BitVec.extractLsb v__0 31 24) (0xB4 : (BitVec 8)))
        then false
        else true

def xlen := 32

def write_CSR (v__26 : (BitVec 12)) : SailM Bool := do
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__26 11 5) (0b1011000 : (BitVec 7)))
       (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__26 4 0)
       ((BitVec.toNat index) ≥b 3) : Bool))
  then (pure true)
  else
    if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__26 11 5) (0b1011100 : (BitVec 7)))
         (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__26 4 0)
         (Bool.and (BEq.beq xlen 32) (((BitVec.toNat index) ≥b 3) : Bool))))
    then (pure true)
    else
      assert false "Pattern match failure at match_bv.sail:36.0-38.1"
      throw Error.Exit

def write_CSR2 (v__30 : (BitVec 12)) : SailM Bool := do
  if (Bool.and (BEq.beq (Sail.BitVec.extractLsb v__30 11 5) (0b1011100 : (BitVec 7)))
       (let index : (BitVec 5) := (Sail.BitVec.extractLsb v__30 4 0)
       (Bool.and (BEq.beq xlen 32) (((BitVec.toNat index) ≥b 3) : Bool))))
  then (pure true)
  else
    assert false "Pattern match failure at match_bv.sail:41.0-43.1"
    throw Error.Exit

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())


end Out.Functions
