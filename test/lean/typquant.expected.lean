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


inductive virtaddr where
  | virtaddr (_ : (BitVec 32))

open virtaddr

abbrev SailM := PreSailM PEmpty.elim trivialChoiceSource Unit

namespace Functions

/-- Type quantifiers: k_ex737# : Bool, k_ex736# : Bool -/
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
  (HAppend.hAppend str (BitVec.toHex x))

/-- Type quantifiers: x : Int -/
def concat_str_dec (str : String) (x : Int) : String :=
  (HAppend.hAppend str (Int.repr x))

/-- Type quantifiers: n : Nat, n > 0 -/
def foo (n : Nat) : (BitVec 4) :=
  (0xF : (BitVec 4))

/-- Type quantifiers: n : Nat, n > 0 -/
def foo2 (n : Nat) : (BitVec n) :=
  (BitVec.zero n)

/-- Type quantifiers: k_n : Int -/
def bar (x : (BitVec k_n)) : (BitVec k_n) :=
  x

def two_tuples (tuple_0 : (String × String)) (tuple_1 : (String × String)) : String :=
  let (x, y) := tuple_0
  let (z, t) := tuple_1
  y

/-- Type quantifiers: tuple_0.2 : Nat, tuple_0.2 ≥ 0 -/
def two_tuples_atom (tuple_0 : (String × Nat)) (tuple_1 : (String × String)) : (BitVec tuple_0.2) :=
  let (x, y) := tuple_0
  let (z, t) := tuple_1
  (BitVec.zero y)

def tuple_of_tuple (tuple_0 : (String × String)) : String :=
  let (s1, s2) := tuple_0
  s1

def use_tuple_of_tuple (s : String) : String :=
  (tuple_of_tuple (s, s))

/-- Type quantifiers: k_nn : Nat, k_nn > 0 -/
def hex_bits_signed2_forwards (bv : (BitVec k_nn)) : (Nat × String) :=
  let len := (Sail.BitVec.length bv)
  let s :=
    if (Eq (BitVec.access bv (HSub.hSub len 1)) 1#1)
    then "stub1"
    else "stub2"
  ((Sail.BitVec.length bv), s)

/-- Type quantifiers: k_nn : Nat, k_nn > 0 -/
def hex_bits_signed2_forwards_matches (bv : (BitVec k_nn)) : Bool :=
  true

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_signed2_backwards (tuple_0 : (Nat × String)) : (BitVec tuple_0.1) :=
  let (notn, str) := tuple_0
  if (BEq.beq str "-")
  then (BitVec.zero notn)
  else let parsed := (BitVec.zero notn)
       if (Eq (BitVec.access parsed (HSub.hSub notn 1)) 0#1)
       then parsed
       else (BitVec.zero notn)

/-- Type quantifiers: tuple_0.1 : Nat, tuple_0.1 > 0 -/
def hex_bits_signed2_backwards_matches (tuple_0 : (Nat × String)) : Bool :=
  let (n, str) := tuple_0
  true

def test_constr (app_0 : virtaddr) : (BitVec 32) :=
  let .virtaddr addr := app_0
  addr

def initialize_registers (_ : Unit) : Unit :=
  ()

end Functions

open Functions

