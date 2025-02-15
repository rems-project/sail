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

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

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

def bitvector_eq (x : (BitVec 16)) (y : (BitVec 16)) : Bool :=
  (Eq x y)

def bitvector_neq (x : (BitVec 16)) (y : (BitVec 16)) : Bool :=
  (Ne x y)

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
  (BitVec.append x y)

def bitvector_add (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (HAdd.hAdd x y)

def bitvector_sub (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (HSub.hSub x y)

def bitvector_not (x : (BitVec 16)) : (BitVec 16) :=
  (Complement.complement x)

def bitvector_and (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (HAnd.hAnd x y)

def bitvector_or (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (HOr.hOr x y)

def bitvector_xor (x : (BitVec 16)) (y : (BitVec 16)) : (BitVec 16) :=
  (HXor.hXor x y)

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

def initialize_registers (_ : Unit) : Unit :=
  ()

