import Out.Sail.Sail
import Out.Sail.BitVec

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 10_000
set_option linter.unusedVariables false

open Sail

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/

inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)

open option

inductive E where | A | B | C
  deriving Inhabited, DecidableEq

open E

inductive Register : Type where
  | r_C
  | r_B
  | r_A
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .r_C => E
  | .r_B => E
  | .r_A => E

open RegisterRef
instance : Inhabited (RegisterRef RegisterType E) where
  default := .Reg r_A
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

/-- Type quantifiers: x : Int -/
def __id (x : Int) : Int :=
  x

/-- Type quantifiers: len : Nat, k_v : Nat, len ≥ 0 ∧ k_v ≥ 0 -/
def sail_mask (len : Nat) (v : (BitVec k_v)) : (BitVec len) :=
  if (LE.le len (Sail.BitVec.length v))
  then (Sail.BitVec.truncate v len)
  else (Sail.BitVec.zeroExtend v len)

/-- Type quantifiers: n : Nat, n ≥ 0 -/
def sail_ones (n : Nat) : (BitVec n) :=
  (Complement.complement (BitVec.zero n))

/-- Type quantifiers: l : Int, i : Int, n : Nat, n ≥ 0 -/
def slice_mask {n : _} (i : Int) (l : Int) : (BitVec n) :=
  if (GE.ge l n)
  then (HShiftLeft.hShiftLeft (sail_ones n) i)
  else let one : (BitVec n) := (sail_mask n (0b1 : (BitVec 1)))
       (HShiftLeft.hShiftLeft (HSub.hSub (HShiftLeft.hShiftLeft one l) one) i)

/-- Type quantifiers: n : Int, m : Int -/
def _shl_int_general (m : Int) (n : Int) : Int :=
  if (GE.ge n 0)
  then (Int.shiftl m n)
  else (Int.shiftr m (Neg.neg n))

/-- Type quantifiers: n : Int, m : Int -/
def _shr_int_general (m : Int) (n : Int) : Int :=
  if (GE.ge n 0)
  then (Int.shiftr m n)
  else (Int.shiftl m (Neg.neg n))

/-- Type quantifiers: m : Int, n : Int -/
def fdiv_int (n : Int) (m : Int) : Int :=
  if (Bool.and (LT.lt n 0) (GT.gt m 0))
  then (HSub.hSub (Int.tdiv (HAdd.hAdd n 1) m) 1)
  else if (Bool.and (GT.gt n 0) (LT.lt m 0))
       then (HSub.hSub (Int.tdiv (HSub.hSub n 1) m) 1)
       else (Int.tdiv n m)

/-- Type quantifiers: m : Int, n : Int -/
def fmod_int (n : Int) (m : Int) : Int :=
  (HSub.hSub n (HMul.hMul m (fdiv_int n m)))

/-- Type quantifiers: k_a : Type -/
def is_none (opt : (Option k_a)) : Bool :=
  match opt with
  | some _ => false
  | none => true

/-- Type quantifiers: k_a : Type -/
def is_some (opt : (Option k_a)) : Bool :=
  match opt with
  | some _ => true
  | none => false

/-- Type quantifiers: k_n : Int -/
def concat_str_bits (str : String) (x : (BitVec k_n)) : String :=
  (HAppend.hAppend str (BitVec.toHex x))

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
  | some x => x
  | none => 0#1

/-- Type quantifiers: y : Int, x : Int -/
def match_pair_pat (x : Int) (y : Int) : Int :=
  match (x, y) with
  | (a, b) => (HAdd.hAdd a b)

/-- Type quantifiers: arg1 : Int, arg0 : Int -/
def match_pair (arg0 : Int) (arg1 : Int) : Int :=
  let x := (arg0, arg1)
  match x with
  | (a, b) => (HAdd.hAdd a b)

def match_reg (x : E) : SailM E := do
  match x with
  | A => readReg r_A
  | B => readReg r_B
  | C => readReg r_C

/-- Type quantifiers: y : Int -/
def match_let (x : E) (y : Int) : SailM Int := do
  match x with
  | A =>
    let x := (HAdd.hAdd y y)
    let z ← do (pure (HAdd.hAdd (HAdd.hAdd y y) (← (undefined_int ()))))
    (pure (HAdd.hAdd z x))
  | B => (pure 42)
  | C => (pure 23)

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg r_A (← (undefined_E ()))
  writeReg r_B (← (undefined_E ()))
  writeReg r_C (← (undefined_E ()))

