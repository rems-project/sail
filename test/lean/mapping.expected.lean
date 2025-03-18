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

inductive word_width where | BYTE | HALF | WORD | DOUBLE
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

open word_width
open option

namespace Functions

def undefined_word_width (_ : Unit) : SailM word_width := do
  (internal_pick [BYTE, HALF, WORD, DOUBLE])

/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def word_width_of_num (arg_ : Nat) : word_width :=
  match arg_ with
  | 0 => BYTE
  | 1 => HALF
  | 2 => WORD
  | _ => DOUBLE

def num_of_word_width (arg_ : word_width) : Int :=
  match arg_ with
  | BYTE => 0
  | HALF => 1
  | WORD => 2
  | DOUBLE => 3

def size_bits_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => (0b00 : (BitVec 2))
  | HALF => (0b01 : (BitVec 2))
  | WORD => (0b10 : (BitVec 2))
  | DOUBLE => (0b11 : (BitVec 2))

def size_bits_backwards (arg_ : (BitVec 2)) : word_width :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then HALF
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then WORD
      else DOUBLE

def size_bits_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true

def size_bits_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then true
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then true
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then true
      else
        if (BEq.beq b__0 (0b11 : (BitVec 2)))
        then true
        else false

def size_bits2_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => (0b00 : (BitVec 2))
  | HALF => (0b01 : (BitVec 2))
  | WORD => (0b10 : (BitVec 2))
  | DOUBLE => (0b11 : (BitVec 2))

def size_bits2_backwards (arg_ : (BitVec 2)) : word_width :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then HALF
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then WORD
      else DOUBLE

def size_bits2_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true

def size_bits2_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then true
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then true
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then true
      else
        if (BEq.beq b__0 (0b11 : (BitVec 2)))
        then true
        else false

def size_bits3_forwards (arg_ : word_width) : (BitVec 2) :=
  match arg_ with
  | BYTE => (0b00 : (BitVec 2))
  | HALF => (0b01 : (BitVec 2))
  | WORD => (0b10 : (BitVec 2))
  | DOUBLE => (0b11 : (BitVec 2))

def size_bits3_backwards (arg_ : (BitVec 2)) : word_width :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then HALF
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then WORD
      else DOUBLE

def size_bits3_forwards_matches (arg_ : word_width) : Bool :=
  match arg_ with
  | BYTE => true
  | HALF => true
  | WORD => true
  | DOUBLE => true

def size_bits3_backwards_matches (arg_ : (BitVec 2)) : Bool :=
  let b__0 := arg_
  if (BEq.beq b__0 (0b00 : (BitVec 2)))
  then true
  else
    if (BEq.beq b__0 (0b01 : (BitVec 2)))
    then true
    else
      if (BEq.beq b__0 (0b10 : (BitVec 2)))
      then true
      else
        if (BEq.beq b__0 (0b11 : (BitVec 2)))
        then true
        else false

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

end Functions
