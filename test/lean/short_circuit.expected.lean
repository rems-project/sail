import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive Register : Type where
  | B
  | R
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .B => Bool
  | .R => Int



abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception



instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg B
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg R
XXXXXXXXX

import Sail
import Out.Defs
import Out.SpecializationV1
import Out.FakeReal

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace Out

open ConcurrencyInterfaceV1

namespace Functions

open option
open Register

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: k_ex1625_ : Bool, k_ex1624_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if ((n ≥b 0) : Bool)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (((n <b 0) && (m >b 0)) : Bool)
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    (if (((n >b 0) && (m <b 0)) : Bool)
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m))

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if ((len ≤b (Sail.BitVec.length v)) : Bool)
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if ((l ≥b n) : Bool)
  then ((sail_ones n) <<< i)
  else
    (let one : (BitVec n) := (sail_mask n (1#1 : (BitVec 1)))
    (((one <<< l) - one) <<< i))

/-- Type quantifiers: n : Nat, n > 0 -/
def to_bytes_le {n : _} (b : (BitVec (8 * n))) : (Vector (BitVec 8) n) := Id.run do
  let res := (vectorInit (BitVec.zero 8))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (vectorUpdate res i (Sail.BitVec.extractLsb b ((8 *i i) +i 7) (8 *i i)))
  (pure loop_vars)

/-- Type quantifiers: n : Nat, n > 0 -/
def from_bytes_le {n : _} (v : (Vector (BitVec 8) n)) : (BitVec (8 * n)) := Id.run do
  let res := (BitVec.zero (8 *i n))
  let loop_i_lower := 0
  let loop_i_upper := (n -i 1)
  let mut loop_vars := res
  for i in [loop_i_lower:loop_i_upper:1]i do
    let res := loop_vars
    loop_vars := (Sail.BitVec.updateSubrange res ((8 *i i) +i 7) (8 *i i) (GetElem?.getElem! v i))
  (pure loop_vars)

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | .some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toFormatted x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

def bump (_ : Unit) : SailM Bool := do
  writeReg R ((← readReg R) +i 1)
  (pure true)

def boom (_ : Unit) : SailM Bool := do
  assert false "not short-circuited"
  throw Error.Exit

/-- Type quantifiers: k_ex1669_ : Bool, k_ex1668_ : Bool -/
def pure_and (a : Bool) (b : Bool) : Bool :=
  (a && b)

/-- Type quantifiers: k_ex1671_ : Bool, k_ex1670_ : Bool -/
def pure_or (a : Bool) (b : Bool) : Bool :=
  (a || b)

/-- Type quantifiers: k_ex1672_ : Bool -/
def effectful_lhs (b : Bool) : SailM Bool := do
  (pure ((← readReg B) && b))

/-- Type quantifiers: k_ex1673_ : Bool -/
def and_effect (b : Bool) : SailM Bool := do
  if (b : Bool)
  then (boom ())
  else (pure false)

/-- Type quantifiers: k_ex1674_ : Bool -/
def or_effect (b : Bool) : SailM Bool := do
  if (b : Bool)
  then (pure true)
  else (bump ())

/-- Type quantifiers: k_ex1676_ : Bool, k_ex1675_ : Bool -/
def chain_and (a : Bool) (b : Bool) : SailM Bool := do
  if (a : Bool)
  then
    (do
      if (b : Bool)
      then (boom ())
      else (pure false))
  else (pure false)

/-- Type quantifiers: k_ex1678_ : Bool, k_ex1677_ : Bool -/
def chain_or (a : Bool) (b : Bool) : SailM Bool := do
  if (a : Bool)
  then (pure true)
  else
    (do
      if ((← (bump ())) : Bool)
      then (pure true)
      else (boom ()))

/-- Type quantifiers: k_ex1680_ : Bool, k_ex1679_ : Bool -/
def mixed (a : Bool) (b : Bool) : SailM Bool := do
  if ((← do
       if (a : Bool)
       then (boom ())
       else (pure false)) : Bool)
  then (pure true)
  else
    (do
      if (b : Bool)
      then (bump ())
      else (pure false))

/-- Type quantifiers: k_ex1681_ : Bool -/
def in_condition (b : Bool) : SailM Int := do
  if ((← do
       if (b : Bool)
       then (boom ())
       else (pure false)) : Bool)
  then (pure 1)
  else
    (do
      if ((← do
           if (b : Bool)
           then (pure true)
           else (bump ())) : Bool)
      then (pure 2)
      else (pure 3))

/-- Type quantifiers: k_ex1682_ : Bool -/
def in_let (b : Bool) : SailM Bool := do
  let x ← do
    if (b : Bool)
    then (bump ())
    else (pure false)
  let y ← do
    if (x : Bool)
    then (pure true)
    else (boom ())
  (pure (x && y))

/-- Type quantifiers: k_ex1683_ : Bool -/
def takes_bool (b : Bool) : Bool :=
  (! b)

/-- Type quantifiers: k_ex1684_ : Bool -/
def as_argument (b : Bool) : SailM Bool := do
  (pure (takes_bool
      (← do
        if (b : Bool)
        then (bump ())
        else (pure false))))

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R (← (undefined_int ()))
  writeReg B (← (undefined_bool ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions
