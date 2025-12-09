import Out.Sail.Sail
import Out.Sail.BitVec

open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

inductive E where | A | B | C
  deriving BEq, Inhabited, Repr
  open E

inductive Register : Type where
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .r_C => E
  | .r_B => E
  | .r_A => E

instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
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

open option
open Register
open E

/-- Type quantifiers: k_ex942_ : Bool, k_ex941_ : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (! (x == y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

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

def undefined_E (_ : Unit) : SailM E := do
  (internal_pick [A, B, C])

def match_enum (x : E) : (BitVec 1) :=
  match x with
  | A => 1#1
  | B => 1#1
  | C => 0#1

def match_option (x : (Option (BitVec 1))) : (BitVec 1) :=
  match x with
  | .some x => x
  | none => 0#1

/-- Type quantifiers: y : Int, x : Int -/
def match_pair_pat (x : Int) (y : Int) : Int :=
  match (x, y) with
  | (a, b) => (a +i b)

/-- Type quantifiers: arg1 : Int, arg0 : Int -/
def match_pair (arg0 : Int) (arg1 : Int) : Int :=
  let x := (arg0, arg1)
  match x with
  | (a, b) => (a +i b)

def match_reg (x : E) : SailM E := do
  match x with
  | A => readReg r_A
  | B => readReg r_B
  | C => readReg r_C

/-- Type quantifiers: y : Int -/
def match_let (x : E) (y : Int) : SailM Int := do
  match x with
  | A =>
    (do
      let x := (y +i y)
      let z ← do (pure ((y +i y) +i (← (undefined_int ()))))
      (pure (z +i x)))
  | B => (pure 42)
  | C => (pure 23)

def match_read (x : E) : SailM Unit := do
  writeReg r_A (← do
    match x with
    | A => readReg r_A
    | B => readReg r_B
    | C => readReg r_C)

def const16 (_ : Unit) : ((BitVec 16) × Bool) :=
  (0xFFFF#16, true)

def const32 (_ : Unit) : ((BitVec 32) × Bool) :=
  (0xEEEEEEEE#32, false)

/-- Type quantifiers: k_n : Nat, k_n ≥ 0 -/
def match_width (x : (BitVec k_n)) : (BitVec (2 * k_n)) :=
  let (foo, _) : ((BitVec k_n) × Bool) :=
    match (Sail.BitVec.length x) with
    | 16 => (const16 ())
    | 32 => (const32 ())
    | n => ((BitVec.zero n), false)
  (foo ++ foo)

def match_option_bitvec (x : (Option (BitVec 16))) : Int :=
  match x with
  | .some 0xFFFF => 1
  | _ => 0

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))

def sail_model_init (x_0 : Unit) : SailM Unit := do
  (initialize_registers ())

end Out.Functions
