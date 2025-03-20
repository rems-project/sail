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

structure My_struct where
  field1 : Int
  field2 : (BitVec 1)
  deriving Inhabited, BEq

/-- Type quantifiers: k_n : Int, k_vasize : Int, k_pa : Type, k_ts : Type, k_arch_ak : Type, k_n > 0
  ∧ k_vasize ≥ 0 -/
structure My_mem_write_request
  (k_n : Nat) (k_vasize : Nat) (k_pa : Type) (k_ts : Type) (k_arch_ak : Type) where
  va : (Option (BitVec k_vasize))
  pa : k_pa
  translation : k_ts
  size : Int
  value : (Option (BitVec (8 * k_n)))
  tag : (Option Bool)
  deriving Inhabited, BEq

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception


XXXXXXXXX

import Out.Sail.Sail
import Out.Sail.BitVec
import Out.Sail.IntRange
import Out.Defs
import Out.Specialization

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail

namespace Out.Functions

open option

/-- Type quantifiers: k_ex760# : Bool, k_ex759# : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (Bool.not (BEq.beq x y))

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if (len ≤b (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if (l ≥b n)
  then ((sail_ones n) <<< i)
  else
    let one : (BitVec n) := (sail_mask n (0b1 : (BitVec 1)))
    (((one <<< l) - one) <<< i)

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if (n ≥b 0)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if (n ≥b 0)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (Bool.and (n <b 0) (m >b 0))
  then ((Int.tdiv (n +i 1) m) -i 1)
  else
    if (Bool.and (n >b 0) (m <b 0))
    then ((Int.tdiv (n -i 1) m) -i 1)
    else (Int.tdiv n m)

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (n -i (m *i (fdiv_int n m)))

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

def undefined_My_struct (_ : Unit) : SailM My_struct := do
  (pure { field1 := (← (undefined_int ()))
          field2 := (← (undefined_bit ())) })

def struct_field2 (s : My_struct) : (BitVec 1) :=
  s.field2

def struct_update_field2 (s : My_struct) (b : (BitVec 1)) : My_struct :=
  { s with field2 := b }

/-- Type quantifiers: i : Int -/
def struct_update_both_fields (s : My_struct) (i : Int) (b : (BitVec 1)) : My_struct :=
  { s with field1 := i, field2 := b }

/-- Type quantifiers: i : Int -/
def mk_struct (i : Int) (b : (BitVec 1)) : My_struct :=
  { field1 := i
    field2 := b }

def undef_struct (x : (BitVec 1)) : SailM My_struct := do
  (undefined_My_struct ())

def match_struct (value : My_struct) : SailM Int := do
  match value with
  | { field2 := 0#1, field1 := g__0 } => (pure 0)
  | { field1 := field1, field2 := 1#1 } => (pure field1)
  | _ =>
    assert false "Pattern match failure at struct.sail:39.4-42.5"
    throw Error.Exit

def initialize_registers (_ : Unit) : Unit :=
  ()

def sail_model_init (x_0 : Unit) : Unit :=
  (initialize_registers ())

