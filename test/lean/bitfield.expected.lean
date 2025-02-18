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

abbrev cr_type := (BitVec 8)

inductive Register : Type where
  | R
  deriving DecidableEq, Hashable
open Register

abbrev RegisterType : Register → Type
  | .R => (BitVec 8)

open RegisterRef
instance : Inhabited (RegisterRef RegisterType (BitVec 8)) where
  default := .Reg R
abbrev SailM := PreSailM RegisterType trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex700# : Bool, k_ex699# : Bool -/
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

def undefined_cr_type (_ : Unit) : SailM (BitVec 8) := do
  (undefined_bitvector 8)

def Mk_cr_type (v : (BitVec 8)) : (BitVec 8) :=
  v

def _get_cr_type_bits (v : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.extractLsbUnif v (HSub.hSub 8 1) 0)

def _update_cr_type_bits (v : (BitVec 8)) (x : (BitVec 8)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v (HSub.hSub 8 1) 0 x)

def _set_cr_type_bits (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 8)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_bits r v)

def _get_cr_type_CR0 (v : (BitVec 8)) : (BitVec 4) :=
  (Sail.BitVec.extractLsbUnif v 7 4)

def _update_cr_type_CR0 (v : (BitVec 8)) (x : (BitVec 4)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 4 x)

def _set_cr_type_CR0 (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 4)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_CR0 r v)

def _get_cr_type_CR1 (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsbUnif v 3 2)

def _update_cr_type_CR1 (v : (BitVec 8)) (x : (BitVec 2)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 3 2 x)

def _set_cr_type_CR1 (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_CR1 r v)

def _get_cr_type_CR3 (v : (BitVec 8)) : (BitVec 2) :=
  (Sail.BitVec.extractLsbUnif v 1 0)

def _update_cr_type_CR3 (v : (BitVec 8)) (x : (BitVec 2)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 1 0 x)

def _set_cr_type_CR3 (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 2)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_CR3 r v)

def _get_cr_type_GT (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsbUnif v 6 6)

def _update_cr_type_GT (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 6 6 x)

def _set_cr_type_GT (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_GT r v)

def _get_cr_type_LT (v : (BitVec 8)) : (BitVec 1) :=
  (Sail.BitVec.extractLsbUnif v 7 7)

def _update_cr_type_LT (v : (BitVec 8)) (x : (BitVec 1)) : (BitVec 8) :=
  (Sail.BitVec.updateSubrange v 7 7 x)

def _set_cr_type_LT (r_ref : (RegisterRef RegisterType (BitVec 8))) (v : (BitVec 1)) : SailM Unit := do
  let r ← do (reg_deref r_ref)
  writeRegRef r_ref (_update_cr_type_LT r v)

def initialize_registers (_ : Unit) : SailM Unit := do
  writeReg R (← (undefined_cr_type ()))

end Functions

open Functions

