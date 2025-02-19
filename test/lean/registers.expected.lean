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

inductive Register : Type where
  | BIT
  | NAT
  | BOOL
  | INT
  | R1
  | R0
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .BIT => (BitVec 1)
  | .NAT => Nat
  | .BOOL => Bool
  | .INT => Int
  | .R1 => (BitVec 64)
  | .R0 => (BitVec 64)

open RegisterRef
instance : Inhabited (RegisterRef RegisterType (BitVec 1)) where
  default := .Reg BIT
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg R0
instance : Inhabited (RegisterRef RegisterType Bool) where
  default := .Reg BOOL
instance : Inhabited (RegisterRef RegisterType Int) where
  default := .Reg INT
instance : Inhabited (RegisterRef RegisterType Nat) where
  default := .Reg NAT
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex873# : Bool, k_ex872# : Bool -/
def neq_bool (x : Bool) (y : Bool) : Bool :=
  (Bool.not (BEq.beq x y))

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

def test (_ : Unit) : SailM Int := do
  writeReg INT (HAdd.hAdd (← readReg INT) 1)
  readReg INT

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R0 (← (undefined_bitvector 64))
  writeReg R1 (← (undefined_bitvector 64))
  writeReg INT (← (undefined_int ()))
  writeReg BOOL (← (undefined_bool ()))
  writeReg NAT (← (undefined_nat ()))
  writeReg BIT (← (undefined_bit ()))

end Functions

open Functions

