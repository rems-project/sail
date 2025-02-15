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

inductive word_width where | BYTE | HALF | WORD | DOUBLE
  deriving Inhabited, DecidableEq

open word_width

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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then HALF
       else if (Eq b__0 (0b10 : (BitVec 2)))
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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then true
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then true
       else if (Eq b__0 (0b10 : (BitVec 2)))
            then true
            else if (Eq b__0 (0b11 : (BitVec 2)))
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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then HALF
       else if (Eq b__0 (0b10 : (BitVec 2)))
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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then true
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then true
       else if (Eq b__0 (0b10 : (BitVec 2)))
            then true
            else if (Eq b__0 (0b11 : (BitVec 2)))
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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then BYTE
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then HALF
       else if (Eq b__0 (0b10 : (BitVec 2)))
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
  if (Eq b__0 (0b00 : (BitVec 2)))
  then true
  else if (Eq b__0 (0b01 : (BitVec 2)))
       then true
       else if (Eq b__0 (0b10 : (BitVec 2)))
            then true
            else if (Eq b__0 (0b11 : (BitVec 2)))
                 then true
                 else false

def initialize_registers (_ : Unit) : Unit :=
  ()

